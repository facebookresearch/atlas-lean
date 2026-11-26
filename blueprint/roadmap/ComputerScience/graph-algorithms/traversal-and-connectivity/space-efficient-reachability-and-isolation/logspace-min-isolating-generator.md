# A logarithmic-space min-isolating weight generator

There is a family of vertex weight assignments on layered vertex sets $\{0, \dots, n\} \times \{0, \dots, w-1\}$, indexed by seeds of length $O(\log (nw))$ depending only on the dimensions, such that (i) for every layered digraph some seed is min-isolating for all reachable pairs; (ii) every weight is bounded by a polynomial in $nw$; and (iii) a single deterministic multitape Turing machine computes the weight of any vertex from the binary dimensions, the vertex coordinates and the seed (read in index order) in space $O(\log(nw))$ (Hoza, Theorem 1.3).

## Proof sketch

Prepare the finite-field context of the Justesen code from the dimensions, stream the seed bits, mask each with a table-free code coordinate, accumulate in base six, and scale by the layer factor with a counted halving loop; every register holds $O(\log(nw))$ bits.

## Depends on

- [Hoza's seeded weight family](hoza-seeded-weight-family.md)
- [The complexity class NL](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/nl.md)

## Proof depends on

- [Some seed min-isolates every layered digraph](all-pairs-min-isolation.md)

## Sources

- W. M. Hoza, "NL = UL", Electronic Colloquium on Computational Complexity, Report TR26-323, 2026.
- J. Justesen, "A Class of Constructive Asymptotically Good Algebraic Codes", IEEE Transactions on Information Theory 18(5), 1972.
