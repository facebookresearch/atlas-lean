# Generic-group lower bounds

Bounds on how often a generic algorithm finds a discrete logarithm, in Nechaev's model: the group has prime order $q$, a permutation of $\mathbb{Z}/q$, fixed or uniform, encodes its elements, and the algorithm is a deterministic decision tree that sees the encodings only through equality tests and pays for each group operation. The bounds follow the proof game of Shoup's Theorem 1 (*Lower Bounds for Discrete Logarithms and Related Problems*, revised version, Section 2), with an explicit constant. The general theorem, for any group order and for randomized algorithms given random identification strings, is [Shoup's generic lower bound for discrete logarithms](../../public-key/hardness-assumptions/shoup-s-generic-lower-bound-for-discrete.md).

- [Distinct affine forms agree at most once](aff-eval-eq-card-le-one.md)
- [Agreement probability of two affine forms](aff-eval-agree-win-prob-le.md)
- [Collision count of a list of affine forms](collision-card-le.md)
- [Generic discrete-logarithm success count, fixed encoding](dlog-success-card-le.md)
- [Generic discrete-logarithm bound, fixed encoding](dlog-win-prob-le.md)
- [Generic discrete-logarithm game](generic-dlog-game.md)
- [Generic discrete-logarithm bound, uniform encoding](generic-dlog-win-prob-le.md)
- [Generic discrete-logarithm bound, squared form](generic-dlog-win-prob-le-sq.md)
