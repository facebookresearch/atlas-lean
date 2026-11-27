# Matching criterion for genetic interactions implied by a partial fitness order

Let $G = \{p_1, \dots, p_t, n_1, \dots, n_s\}$ be a set of $k = t + s$ genotypes with fitnesses $W = (w_g)_{g \in G}$. A **genetic interaction** is an integer linear form (a contrast)

$$f(W) = \sum_{i=1}^{t} c_i\, w_{p_i} - \sum_{j=1}^{s} d_j\, w_{n_j}, \qquad c_i, d_j \in \mathbb{Z}_{>0}, \quad \sum_i c_i = \sum_j d_j;$$

the landscape has positive $f$-interaction if $f(W) > 0$. This covers Fourier–Walsh coefficients, interaction coordinates and circuit interactions. A partial order $P = (G, \prec)$ **implies positive $f$-interaction** if $f(W) > 0$ for every $W$ with $w_g < w_h$ whenever $g \prec h$.

**Theorem.** $P$ implies positive $f$-interaction if and only if the multiset in which each $p_i$ appears $c_i$ times and each $n_j$ appears $d_j$ times can be partitioned into pairs $(p_i, n_j)$ with $p_i \succ n_j$; equivalently, the bipartite graph with these copies as vertices and an edge whenever $p_i \succ n_j$ has a perfect matching.

**Corollaries.**
- (Linear orders; due to Crona et al. 2017.) For a total order, the criterion says that the word obtained by reading genotypes from fittest to least fit, writing $c_i$ letters $P$ for $p_i$ and $d_j$ letters $N$ for $n_j$, is a Dyck word starting with $P$.
- (Algorithm.) With $m = \sum_i c_i$ (the positive coefficients of $f$ counted with multiplicity), whether a partial order implies positive $f$-interaction can be decided in $O(m^3)$ time: build the comparability bipartite graph by breadth-first search on the Hasse diagram and run Hopcroft–Karp in $O(m^{5/2})$. This is exponentially faster than enumerating linear extensions.
- (Sparsity.) For forms with coefficients $\pm 1$, the fraction of labelled partial orders on $k$ elements that imply $f$-interaction is at most $4/k$, hence tends to $0$ as $k \to \infty$.

## Depends on

- [Reciprocal sign epistasis, multiple peaks and the small-face limitation](../epistasis-and-landscape-structure.md)

## Expansion

Sufficiency: if the pairing exists, $f(W) = \sum_{\text{pairs}} (w_{p_i} - w_{n_j})$ and every summand is positive. Necessity is a Hall-type argument: if no perfect matching exists, Hall's condition fails for some set of $n$-copies, and one builds a fitness vector consistent with $P$ (an up-set of the order pushed high, its complement low) on which $f \le 0$. The sparsity bound uses that within one isomorphism class of posets, any relabelling that makes the poset imply interaction must do the same to a fixed linear extension, and only $k! \cdot 2/(k/2+1) \le 4(k-1)!$ linear orders imply interaction.

## Sources

- C. Lienkaemper, L. Lamberti, J. Drain, N. Beerenwinkel, A. Gavryushkin, *The geometry of partial fitness orders and an efficient method for detecting genetic interactions*, J. Math. Biol. 77 (2018), 951–970 (Section 2, Definition 1, Theorems 1–4). <https://doi.org/10.1007/s00285-018-1237-7> (PMCID: PMC6153669)
