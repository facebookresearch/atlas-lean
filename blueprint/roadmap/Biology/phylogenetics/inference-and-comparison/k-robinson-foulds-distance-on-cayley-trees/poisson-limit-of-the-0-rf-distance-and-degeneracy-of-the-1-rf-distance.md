# Poisson limit of the 0-RF distance and degeneracy of the 1-RF distance

A *Cayley tree on $[n]$* is a tree with vertex set $[n] = \{1, \dots, n\}$; there are $n^{n-2}$ of them. For $k \in \{0, \dots, n-2\}$, the *$k$-local split* of a tree $T$ at edge $e = \{u, v\}$ is the pair $A \mid B$, where $A$ (resp. $B$) is the set of vertices of $T \setminus e$ within distance $k$ of $u$ (resp. $v$). The *$k$-RF distance* is

$$d_{k\text{-RF}}(T, T') = 2(n-1) - 2S_k(T, T'),$$

where $S_k(T, T')$ is the number of $k$-local splits shared by $T$ and $T'$; it is a metric. A $0$-local split is an edge, and an $(n-2)$-local split is an ordinary split (bipartition obtained by deleting an edge). Throughout, $\mathcal T, \mathcal T'$ are independent uniform random Cayley trees on $[n]$.

**Lemma (forest extensions).** The number of Cayley trees on $[n]$ containing a given spanning forest with $m$ trees of sizes $q_1, \dots, q_m$ is $q_1 \cdots q_m\,n^{m-2}$. Hence a fixed set of $j$ pairwise disjoint pairs from $[n]$ are all edges of a uniform Cayley tree with probability exactly $(2/n)^j$.

**Theorem (0-RF).** Let $S'_n = S_0(\mathcal T, \mathcal T')$ be the number of edges shared by $\mathcal T$ and $\mathcal T'$. Then $\mathbb E(S'_n) = 2(n-1)/n$, $\mathrm{Var}(S'_n) \sim 2$, and the total variation distance between $S'_n$ and a Poisson variable with mean $2$ is $O(1/n)$. Consequently

$$(n - 1) - \tfrac12 d_{0\text{-RF}}(\mathcal T, \mathcal T') = S'_n \xrightarrow{d} \mathrm{Poisson}(2).$$

The same Poisson$(2)$ limit holds for the number of edges of a fixed or random Cayley tree that appear among $n-1$ pairs chosen uniformly at random without replacement.

**Theorem (1-RF).** The expected number of $1$-local splits shared by $\mathcal T$ and $\mathcal T'$ is $O(1/n)$. Hence $d_{1\text{-RF}}(\mathcal T, \mathcal T')$ converges in distribution to the constant $2n - 2$, the maximum possible value.

## Depends on

- [Central limit theorem for the (n-2)- and (n-3)-RF distances](central-limit-theorem-for-the-n-2-and-n-3-rf-distances.md)

## Expansion

Each of the $\binom n2$ pairs is an edge of a uniform Cayley tree with probability $2/n$, so it is an edge of both independent trees with probability $4/n^2$, giving mean $2(n-1)/n \to 2$; the indicators are dissociated and nearly independent, and the Stein-Chen bound gives the Poisson approximation with rate $O(1/n)$. A shared $1$-local split requires an edge together with the full neighborhoods of both endpoints to coincide in the two trees, which is much less likely, so the $1$-RF distance is asymptotically maximal. The three regimes (normal at $k = n-2, n-3$, Poisson at $k = 0$, degenerate at $k = 1$) explain the simulation patterns that motivated the metric.

## Sources

- M. Fuchs and M. Steel, "The asymptotic distribution of the k-Robinson-Foulds dissimilarity measure on labelled trees", *Journal of Computational Biology* 32(11) (2025), 1060–1073, Proposition 5, Corollaries 6 and 7, Theorem 8, Proposition 9, Proposition 11, Theorem 16 and Corollary 17, <https://doi.org/10.1089/cmb.2025.0093> (preprint arXiv:2412.20012).