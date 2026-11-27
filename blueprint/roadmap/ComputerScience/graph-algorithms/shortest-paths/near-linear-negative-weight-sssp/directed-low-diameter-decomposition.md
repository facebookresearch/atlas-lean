# Weak and strong directed low-diameter decompositions with overhead rho

Let $G=(V,E,w)$ be a directed graph with nonnegative weights and let $D>0$. A *weak low-diameter decomposition (LDD) with overhead $\rho=\rho(n)$* is a randomized (Las Vegas) algorithm that, given $G$ and $D$, outputs an edge set $S\subseteq E$ such that

1. (sparse hitting) for every $e\in E$, $\Pr[e\in S]\le O\big(\rho\, w(e)/D+n^{-c}\big)$ for a constant $c\ge 1$ fixed in advance (the events need not be independent);
2. (weak diameter) every strongly connected component $C$ of $G\setminus S$ satisfies $\mathrm{dist}_G(u,v)\le D$ for all $u,v\in C$.

The decomposition is *strong* if moreover $\mathrm{dist}_{G\setminus S}(u,v)\le D$ for all $u,v$ in a common strongly connected component of $G\setminus S$.

This is the definition of Bringmann, Cassis and Fischer, whose sparse-hitting bound allows the additive $n^{-c}$ term. The stronger notion of Bringmann, Fischer, Haeupler and Latypov, a directed LDD *with loss $L$*, is stated for positive weights and $D\ge 1$: it is a probability distribution over edge sets $S\subseteq E$ with the weak-diameter property 2 and the pure bound $\Pr[e\in S]\le L\,w(e)/D$ for every $e\in E$, with no additive term.

## Depends on

- [SCC partition](../../traversal-and-connectivity/strongly-connected-components/is-sccpartition.md)
- [Las Vegas and Monte Carlo algorithms](../../../randomized-algorithms/probabilistic-analysis-tools/las-vegas-and-monte-carlo-algorithms.md)

## Sources

- Karl Bringmann, Alejandro Cassis, Nick Fischer, "Negative-Weight Single-Source Shortest Paths in Near-Linear Time: Now Faster!", FOCS (2023), arXiv:2304.05279.
- Aaron Bernstein, Danupon Nanongkai, Christian Wulff-Nilsen, "Negative-Weight Single-Source Shortest Paths in Near-linear Time", FOCS (2022), arXiv:2203.03456.
- Karl Bringmann, Nick Fischer, Bernhard Haeupler, Rustam Latypov, "Near-Optimal Directed Low-Diameter Decompositions", ICALP (2025), arXiv:2502.05687.
