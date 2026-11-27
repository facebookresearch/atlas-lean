# A Seidel-type algorithm for violator spaces

Let $(H, \mathrm{cl})$ be a violator space with $n$ constraints and combinatorial dimension $\delta$, accessed through a *violation test* (does $f$ violate the basis $B$?) and a *basis computation* on sets of at most $\delta(\delta + 1)$ constraints. The algorithm solveVS, a variant of Seidel's randomized incremental algorithm, inserts the constraints in a uniformly random order; every basis computation of a call includes its set $W$ of witness constraints, and when the $i$-th constraint $f_i$ violates the current basis $B_{i-1}$, the call recurses on $f_1, \dots, f_i$ with the witness set $W \cup B_{i-1} \cup \{f_i\}$, so that the recursion depth is at most $\delta$. Started with $W = \emptyset$, it computes a basis of $H$ with an expected $O(\delta^{\delta + 1} n)$ violation tests and an expected $O((\delta \ln n)^\delta)$ basis computations. For constant $\delta$ and constant-time primitives it runs in expected $O(n)$ time.

## Depends on

- [Violator space](violator-space.md)
- [Uniformly random rearrangement of a list](../../randomized-algorithms/average-case-running-time/uniform-permutation.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Linear programming in low dimensions" (Chapter 22), <https://sarielhp.org/book/chapters/lp.pdf>: Section 22.6.2.1 (solveVS, "a variant of Seidel's algorithm", Figure 22.5), Lemma 22.6.8 (recursion depth at most $\delta$) and Theorem 22.6.9 (its expected numbers of violation tests and basis computations); Section 22.7 treats Clarkson's algorithm for violator spaces separately
