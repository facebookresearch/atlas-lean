# Dead-end elimination for protein design

Computational protein design searches over amino acid identities and side-chain conformations (rotamers) at each designed residue to minimize a pairwise-decomposable energy. Dead-end elimination (DEE) criteria discard rotamers that provably cannot belong to the global minimum energy conformation, before an exact search such as A* enumerates what remains.

- [Interval MinDEE pruning for continuous rotamers](interval-mindee-pruning-for-continuous-rotamers.md)
