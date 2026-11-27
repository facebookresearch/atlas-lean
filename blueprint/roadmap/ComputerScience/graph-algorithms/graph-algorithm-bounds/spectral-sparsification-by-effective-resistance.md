# Spectral sparsification by effective-resistance sampling

Let $G = (V, E, w)$ be a connected graph with $n \ge 2$ vertices and positive edge weights, and Laplacian $L_G$, and for an edge $e$ let $R_{\mathrm{eff}}(e)$ be its effective resistance, so that $\sum_e w_e R_{\mathrm{eff}}(e) = n - 1$ (Foster's theorem). Every edge has $R_{\mathrm{eff}}(e) > 0$. Let $1/\sqrt n < \varepsilon \le 1$ and sample $q = \lceil 9 C^2 n \log n / \varepsilon^2 \rceil$ edges, where $C$ is the absolute constant of the matrix concentration bound used in the proof, independently with replacement, choosing $e$ with probability $p_e = w_e R_{\mathrm{eff}}(e)/(n-1)$, and add each sampled copy of $e$ to $H$ with weight $w_e/(q p_e)$. Then $\mathbb{E}[L_H] = L_G$, and if $n$ is sufficiently large, with probability at least $1/2$, $(1 - \varepsilon) L_G \preceq L_H \preceq (1 + \varepsilon) L_G$.

## Depends on

- [Spectral approximation of graphs](../../../GraphTheory/algebraic-graph-theory/part-02/spectral-sparsification/spectral-approximation-of-graphs.md)
- [Effective resistance is a potential difference](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/effective-resistance-eq-sub-of-laplacian.md)

## Proof depends on

- [Foster's identity](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/sum-mul-effective-resistance.md)

## Expansion

This page becomes ready once:

- Matrix Chernoff bound for sums of independent positive semidefinite random matrices, applied on the subspace orthogonal to the all-ones vector (proof prerequisite; not yet stated)

## Sources

- D. A. Spielman and N. Srivastava, "Graph sparsification by effective resistances", *SIAM Journal on Computing* 40(6):1913–1926, 2011
- J. A. Tropp, "An introduction to matrix concentration inequalities", *Foundations and Trends in Machine Learning* 8(1–2):1–230, 2015
