# Tree sizes and height of the Kingman forest of a dense random graph

Let $F(G_{n,p})$ be the Kingman forest of the Erdős–Rényi graph $G_{n,p}$ (Kingman's coalescent run on $G_{n,p}$, with mergers allowed only along edges), let $C_{n,p}$ be its number of trees and $C_p$ the limit law of $C_{n,p}$. For a vertex $v$ let $\mathrm{ht}(v)$ be its graph distance to the root of its tree and $\mathrm{ht}(F) = \max_v \mathrm{ht}(v)$.

**Theorem 1.3.** Fix $p \in (0,1)$.

1. Let $X_n = (|T_1|, \dots, |T_{C_{n,p}}|)$ be the tree sizes of $F(G_{n,p})$ in uniformly random order. Then
$$\Big(\tfrac{1}{n} X_n,\ C_{n,p}\Big) \xrightarrow{d} (X, C_p),$$
where, conditionally on $C_p$, $X$ is uniform on the unit simplex of dimension $C_p - 1$, i.e. $X \sim \mathrm{Dirichlet}(1, \dots, 1)$ with $C_p$ parameters.
2. There is $K > 0$ such that for all $n$,
$$\Big|\, \mathbb{E}[\mathrm{ht}(F(G_{n,p}))] - e \log n + \tfrac{3}{2} \log\log n \,\Big| \le K, \qquad \frac{\mathrm{ht}(F(G_{n,p}))}{e \log n} \xrightarrow{\ \mathbb{P}\ } 1 .$$

In genealogical terms: the surviving lineages split the sample into families whose proportions are as in Kingman's coalescent stopped with $C_p$ blocks (uniform on the simplex), and the forest has the logarithmic height of a random recursive tree.

## Depends on

- [Number of trees in the Kingman forest of an Erdős–Rényi graph](number-of-trees-in-the-kingman-forest-of-an-erdos-renyi-graph.md)

## Expansion

Because edge presence is independent of the order in which $\mathrm{Kingman}(K_n)$ proposes mergers, the Kingman forest of $G_{n,p}$ can be coupled with the forest built by $\mathrm{Kingman}(K_n)$, the two agreeing in their large-scale structure (tree sizes and heights) while $C_{n,p}$ stays tight. For the complete graph, the block sizes when $k$ blocks remain are uniform on the simplex (the Pólya-urn description of Kingman's coalescent), and the forest built by $\mathrm{Kingman}(K_n)$ is a random recursive tree, whose height is $e \log n - \frac{3}{2}\log\log n + O(1)$. Transferring through the coupling gives both statements.

## Sources

- L. Addario-Berry, C. Atamanchuk, M. Kaye, "Kingman's coalescent on a random graph", arXiv:2509.16181 (2025), Theorems 1.1, 1.2 and 1.3, <https://doi.org/10.48550/arXiv.2509.16181>.
