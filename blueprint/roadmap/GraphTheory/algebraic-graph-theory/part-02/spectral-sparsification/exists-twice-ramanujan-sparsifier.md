# Twice-Ramanujan sparsifiers

Let $V$ and $E$ be finite sets and let each $e \in E$ be an edge from $e^-$ to $e^+$ in $V$ (a finite multigraph; loops $e^- = e^+$ are allowed), with nonnegative weights $w : E \to [0, \infty)$ and $n = \lvert V\rvert$, and let $d > 1$ be real. Then there are weights $w' : E \to [0, \infty)$, with $w'_e = 0$ whenever $w_e = 0$, at most $\lceil d(n - 1) \rceil$ of them nonzero (where $n - 1$ is read as $0$ when $n = 0$), such that

$$L_w \preccurlyeq L_{w'} \preccurlyeq \kappa\, L_w, \qquad \kappa = \frac{d + 1 + 2\sqrt d}{d + 1 - 2\sqrt d},$$

where $L$ is the weighted [Laplacian](../../part-01/graph-laplacians-and-cheeger-s-inequality/laplacian.md) and $\preccurlyeq$ the Loewner order (Batson, Spielman and Srivastava, *Twice-Ramanujan sparsifiers*, arXiv:0808.0163, Theorem 1.1). The source states it for weighted graphs; the multigraph form follows by merging parallel edges.

## Informally uses

- [Batson–Spielman–Srivastava, vector form](exists-sparse-reweighting.md): the proof of Theorem 1.1 writes $L_G = B^{\mathsf T} W B$ and applies Theorem 3.1, on $\operatorname{im}(L_G)$, to the columns of $(L_G^+)^{1/2} B^{\mathsf T} W^{1/2}$, one per edge.
