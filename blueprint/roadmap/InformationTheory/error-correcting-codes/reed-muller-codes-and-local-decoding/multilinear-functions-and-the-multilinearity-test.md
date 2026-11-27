# Multilinear functions on F^n and the multilinearity test

Let $\mathbb{F}$ be a field and $n \ge 1$. A function $f : \mathbb{F}^n \to \mathbb{F}$ is multilinear if its restriction to every axis-parallel line, $t \mapsto f(x_1, \dots, x_{i-1}, t, x_{i+1}, \dots, x_n)$, is an affine function of $t$. Equivalently, $f$ is the evaluation of a polynomial of degree at most one in each variable, namely the multilinear extension of its values on $\{0, 1\}^n$. For $\delta \ge 0$, a line is $\delta$-approximately affine for $f$ if some affine function agrees with $f$ on all but at most $\delta|\mathbb{F}|$ of its points. The multilinearity test picks a uniformly random direction $i$ and point $x$, reads $f$ on the axis-parallel line through $x$ in direction $i$, and accepts if that restriction is affine.

## Depends on

- [Multilinear extension of a Boolean function](../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- L. Babai, L. Fortnow, C. Lund, "Non-Deterministic Exponential Time Has Two-Prover Interactive Protocols", Computational Complexity, 1991.
