# Clarkson's algorithm for violator spaces

Let $(H, \mathrm{cl})$ be a violator space with $n$ constraints and combinatorial dimension $\delta$, accessed through a *violation test* (does $f$ violate the basis $B$?) and a *basis computation* on sets of at most $\delta(\delta + 1)$ constraints. Clarkson's randomized algorithm computes a basis of $H$ with an expected $O(\delta^{\delta + 1} n)$ violation tests and an expected $O((\delta \ln n)^\delta)$ basis computations. For constant $\delta$ and constant-time primitives it runs in expected $O(n)$ time.

## Depends on

- [Violator space](violator-space.md)

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Linear programming in low dimensions" (Chapter 22), <https://sarielhp.org/book/chapters/lp.pdf>: Theorem 22.6.9 (analysis of solveVS, Figure 22.5)
