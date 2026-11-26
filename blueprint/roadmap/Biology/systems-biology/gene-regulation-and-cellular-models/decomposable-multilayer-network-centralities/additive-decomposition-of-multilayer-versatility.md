# Additive decomposition of multilayer versatility

In a multilayer network with supra-adjacency $M = A + C$ (within-layer part $A$, between-layer part $C$), $L$ layers of $n$ nodes each ($N = nL$), and $0 \le p < 1$ with $\rho(pM) < 1$, let $x$, $l$, $g$, $l_i$, $g_i$ and the local-set and query-set vectors $l_i^{(k)}$, $g_i^{(k)}$ be the versatility, local, global, layer-specific and query-set centralities defined by their PageRank-type fixed-point equations.

**Theorem (decomposability).**

1. Versatility splits into local and global centrality: $l + g = (L + 1)\, x$.
2. Global centrality splits over target layers: $\sum_{i=1}^{L} g_i = g$, and similarly $\sum_{i=1}^{L} l_i = l$.
3. If the sets $Q_1, \dots, Q_K$ partition the nodes of layer $i$, then $\sum_{k=1}^{K} l_i^{(k)} = l_i$ and $\sum_{k=1}^{K} g_i^{(k)} = g_i$.

## Depends on

- [Local and global PageRank centralities of multilayer networks](local-and-global-pagerank-centralities-of-multilayer-networks.md)

## Expansion

Each identity follows from linearity and uniqueness of the fixed points. For (1), add the equations for $l$ and $g$: $l + g = p\big[Al + Cl + (A + C)g\big] + (1-p)\big(\tfrac1n + \tfrac1N\big)\mathbf{1} = pM(l + g) + \tfrac{(L+1)(1-p)}{N}\mathbf{1}$, using $1/n = L/N$; the unique solution is $(L+1)(I - pM)^{-1}\tfrac{1-p}{N}\mathbf{1} = (L+1)x$. For (2), summing the layer-specific equations over $i$ uses $\sum_i \mathbf{1}^{[i]} = \mathbf{1}$ and $\sum_i l_i = l$ (because $A$ is block diagonal), so the sum solves the equation for $g$. For (3), summing over a partition uses $\sum_k \mathbf{1}_{Q_k} = \mathbf{1}^{[i]}$, first for the local-set vectors and then for the query-set vectors. Because centralities are used only as rankings, the factor $L + 1$ in (1) is immaterial: the global centrality of a gene is exactly its versatility minus its purely within-tissue part, and it further splits into contributions toward each tissue and each query set.

## Sources

- T. Kumar, R. Sethuraman, S. Mitra, B. Ravindran, M. Narayanan, "MultiCens: Multilayer network centrality measures to uncover molecular mediators of tissue-tissue communication", PLoS Computational Biology (2023), Methods: Eqs. 1-10 (supra-adjacency decomposition, versatility, local, global, layer-specific, local-set and query-set centralities), Lemmas 1-4 and Theorem 1 (convergence), Lemmas 5-8 and Theorem 2 (decomposability, Eqs. 11-14). <https://doi.org/10.1371/journal.pcbi.1011022> (PMC10159362)
