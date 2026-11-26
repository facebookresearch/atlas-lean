# Coset complexes of a group with a family of subgroups

Let $G$ be a finite group and $K_0, \dots, K_d$ subgroups of $G$. The **coset complex** $\mathcal{CC}(G; K_0, \dots, K_d)$ is the $(d)$-dimensional simplicial complex whose vertices are the cosets $gK_i$ ($g \in G$, $0 \le i \le d$), and in which a set of vertices $\{g_0 K_{i_0}, \dots, g_j K_{i_j}\}$ with distinct types $i_0, \dots, i_j$ is a face if and only if

$$
\bigcap_{\ell = 0}^{j} g_\ell K_{i_\ell} \ne \emptyset.
$$

The complex is $(d+1)$-partite (coloured by type), and $G$ acts on it by left multiplication, transitively on top faces.

## Depends on

- [Finite abstract simplicial complex](../rational-homology-of-simplicial-complexes/is-simplicial-complex.md)

## Sources

- T. Kaufman, I. Oppenheim, "Construction of new local spectral high dimensional expanders", STOC (2018); Combinatorica 43 (2023), arXiv:1710.05304.
- A. Lubotzky, "High dimensional expanders", Proceedings of the ICM (2018), arXiv:1712.02526.
