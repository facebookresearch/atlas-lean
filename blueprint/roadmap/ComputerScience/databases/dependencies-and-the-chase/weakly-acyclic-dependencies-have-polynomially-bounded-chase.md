# Weakly acyclic dependencies have polynomially bounded chase

Let $\Sigma$ be the union of a weakly acyclic set of tuple-generating dependencies (no cycle of the
dependency graph on positions passes through a special edge) and a set of equality-generating
dependencies. Then, for fixed $\Sigma$, there is a polynomial in the size of the input instance that bounds the length of every
chase sequence. In data exchange with such target dependencies, a universal solution exists if and only if
the chase does not fail, and it can then be computed in polynomial time.

## Depends on

- [Tuple- and equality-generating dependencies and the chase](tuple-and-equality-generating-dependencies-and-the-chase.md)

## Sources

- R. Fagin, Ph. G. Kolaitis, R. J. Miller and L. Popa, *Data exchange: semantics and query answering*, Theoret. Comput. Sci. 336 (2005) 89–124, Theorem 3.9 and Corollary 3.10. <https://www.cis.upenn.edu/~val/CIS650/DataX-tcs.pdf>
