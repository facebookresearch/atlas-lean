# Dimension of the space of low-degree functions

Over any field $\mathbb{F}$, the squarefree monomials $\prod_{i \in S} x_i$, $S \subseteq [n]$, form a basis of the functions $\{0,1\}^n \to \mathbb{F}$. Consequently the space of functions of degree at most $d$ has dimension exactly $\sum_{j = 0}^{d}\binom{n}{j}$, and its codimension is $\sum_{j > d}\binom{n}{j} = \sum_{j < n - d}\binom{n}{j}$, the dimension of the degree-$(n - d - 1)$ space.

## Proof sketch

The $2^n$ monomials span all functions (interpolation at points via indicator polynomials) and the space has dimension $2^n$, so they are independent; restricting to $|S| \le d$ gives the count, and complementation $S \mapsto [n]\setminus S$ gives the codimension identity.

## Depends on

- [Multilinear extension](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/multilinear-extension.md)
- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
- R. Smolensky, "Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Complexity", STOC 1987.
