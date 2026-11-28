# Static polynomial evaluation problem

For a finite field $\mathbb{F}$ and $n \ge 1$, the *polynomial evaluation problem* takes as input a polynomial $P \in \mathbb{F}[X]$ of degree at most $n$, given by its coefficients, and answers queries $x \in \mathbb{F}$ with $P(x)$. Any $n + 1$ evaluations at distinct points determine $P$ by Lagrange interpolation.

## Depends on

- [Static cell-probe structure with space $S$ and query time $t$](static-cell-probe-structure.md)

## Sources

- Kasper Green Larsen, "Higher Cell Probe Lower Bounds for Evaluating Polynomials", FOCS (2012).
