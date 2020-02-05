import freegroups.freegroup as fg
import freegroups.whiteheadgraph as wg
from collections import deque
from fractions import Fraction
import itertools
import networkx as nx
import math

def smallcancellation(relators,theCp=None):
    """
    Check if the relators satisfy any of several small cancellation conditions that guarantee hyperbolicity.
    """
    F,rels=fg.parseinputwords(relators)
    if theCp is None:
        theCp=Cprime(rels)
    if theCp<Fraction(1,6):
        return True
    theT=T(rels)
    Cest=int(math.ceil(Fraction(theCp.denominator,theCp.numerator)))
    if (Cest>=5 and theT>=4) or (Cest>=4 and theT>=5) or (Cest>=3 and theT>=7):
        return True
    theC=C(rels,7)
    if (theC>=7) or (theC>=5 and theT>=4) or (theC>=4 and theT>=5) or (theC>=3 and theT>=7):
        return True
    else:
        return False

def Cprime(relators,Lambda=1):
    """
    Calculate the largest ratio of piece length to length of relator containing it.

    Stop and return 1 if we find any such ratio >= 1/Lambda.
    """
    F,rels=fg.parseinputwords(relators)
    biggestratio=Fraction(1,min(len(r) for r in rels))
    if biggestratio>=Fraction(1,Lambda):
        return 1
    rels.sort(key=len) # sort list of relators with shortest first
    irels=[rel for rel in itertools.chain.from_iterable(zip([w() for w in rels],[(w**(-1))() for w in rels]))] # arrange relators and inverses in a list of the form relator1, inverse of relator1, relator2, inverse of relator2,...
    drels=[x+x for x in irels]
    for relatorindex in range(len(rels)):
        relator=irels[2*relatorindex]
        foundbiggest=False
        for L in range(len(relator),int(biggestratio*len(relator)),-1):# only check subwords of length L that would give biggest ratio if they were a piece
            for startingindex in range(len(relator)):
                p=(relator+relator)[startingindex:startingindex+L] # the subword of length L starting at index i in reltaor as a cyclic word
                # now we need to check if p is a piece
                # we do not need to check lower relatorindices, because we already scanned those relators for pieces
                if any(p in x for x in [(relator+relator)[startingindex+1:len(relator)+startingindex+L-1]]+[drels[i] for i in range(2*relatorindex+1,len(drels))]):# found a matching subword, p is a piece
                    biggestratio=Fraction(len(p),len(relator))
                    foundbiggest=True
                    if biggestratio>=Fraction(1,Lambda):
                        return 1
                    break
            if foundbiggest: # if we found the biggest piece in this relator we can move on to the next relator. 
                break
    return biggestratio

def T(relators):
    F,rels=fg.parseinputwords(relators)
    G=nx.Graph(wg.WGraph(rels))
    theedges=[e for e in G.edges()]
    shortestcycle=float('inf')
    for e in theedges:
        G.remove_edge(*e)
        try:
            shortestcycleusinge=1+nx.shortest_path_length(G,*e)
        except NetworkXNoPath:
            shortestcycleusinge=float('inf')
        G.add_edge(*e)
        shortestcycle=min(shortestcycle,shortestcycleusinge)
    return shortestcycle


    
def C(relators,quit_at=float('inf')):
    """
    FInd the minimum number p such that there exists some cyclic permutation of some relator that can be expressed as a freely reduced product of p pieces.

    If quit_at=q is specified the algorithm will stop and return q once it is determined that p>=q.
    Relators should already be cyclically reduced.
    """
    F,rels=fg.parseinputwords(relators)
    thepieces=pieces(rels)
    minnumberpieces=quit_at
    def min_string_piece_expression(whatsleft,thepieces,quit_at):
        # recursively determine the minimal expression of the string whatsleft as a concatenation of elements of thepieces, or stop once it is determined that any such expression requires at least quit_at pieces
        if not whatsleft:
            return 0
        minexp=quit_at
        for p in thepieces:
            if p!=whatsleft[:len(p)]:
                continue
            else:
                minexp=min(minexp,1+min_string_piece_expression(whatsleft[len(p):],thepieces,minexp-1))
        return minexp
    def min_relator_piece_expression(relator,thepieces,quit_at):
        r=relator()
        minexp=quit_at
        # first find a piece p such that for relator r we can write p=xy and r=yzx, with y nontrivial
        for p in thepieces:
            if len(p)>len(r):
                continue
            possiblestartingindices=[] # for given p there may be different possible choices of y
            for startingindex in range(len(r)-len(p)+1,len(r)+1):
                if p==(r+r)[startingindex:startingindex+len(p)]:
                    possiblestartingindices.append(startingindex)
            if not possiblestartingindices:
                continue
            for startingindex in possiblestartingindices:
                # found a way to fit p into r spanning the beginning of r. This accounts for x and y part of r. Now recursively find shortest expression of z=whatsleft as a concatenation of pieces.
                whatsleft=(r+r)[startingindex+len(p):startingindex+len(r)]
                if not whatsleft:
                    return 1
                else:
                    minexp=min(minexp,1+min_string_piece_expression(whatsleft,thepieces,minexp-1))
        return minexp
    for thisrelator in rels:
        minnumberpieces=min(minnumberpieces,min_relator_piece_expression(thisrelator,thepieces,minnumberpieces))
    return minnumberpieces


        
def pieces(relators):
    """
    Given input container of relators, return set of pieces, which are subwords occuring more than once in relators or their inverses, as cyclic words.
    """
    F,rels=fg.parseinputwords(relators)
    pieces=set()
    irels=[rel for rel in itertools.chain.from_iterable(zip([w() for w in rels],[(w**(-1))() for w in rels]))] # arrange relators and inverses in a list of the form relator1, inverse of relator1, relator2, inverse of relator2,...
    drels=[x+x for x in irels]
    for relatorindex in range(len(rels)): # only need to search relators for candidate pieces, since a piece contained in inverse will be inverse of piece contained in relator
        relator=irels[2*relatorindex]
        for L in range(1,1+len(relator)):
            for startingindex in range(len(relator)):
                p=(relator+relator)[startingindex:startingindex+L] # the subword of length L starting at index i in reltaor as a cyclic word
                # now we need to check if p is a piece
                # we do not need to check lower relatorindices, because we already scanned those relators for pieces
                if any(p in x for x in [(relator+relator)[startingindex+1:len(relator)+startingindex+L-1]]+[drels[i] for i in range(2*relatorindex+1,len(drels))]):# found a matching subword, p is a piece
                    pieces.add(p)
                    pieces.add(''.join(reversed(p.swapcase())))
    return pieces


        
        
    
    
    
                
