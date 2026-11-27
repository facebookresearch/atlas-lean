# Weighted matrix-tree theorem

Let $G$ be a finite simple graph with vertex set $V$ and $c$ a real function on unordered pairs of vertices. For every vertex $x$,

$$\sum_{T} \prod_{e \in T} c(e) = \det \Delta_G^{(x)},$$

where $T$ runs over the spanning trees of $G$, $\Delta_G$ is the network Laplacian, with $\sum_{y} c(xy)$ (over the neighbours $y$ of $x$) on the diagonal and $-c(xy)$ at the entries of edges $xy$, and $\Delta_G^{(x)}$ is $\Delta_G$ with the row and column of $x$ removed (R. Lyons and Y. Peres, *Probability on Trees and Networks*, Cambridge University Press 2016, corrected online version of 19 August 2026, Section 4.4, the paragraph before Exercise 4.16, stated there for simple networks; the network Laplacian is that of Exercise 2.62). The network Laplacian is the [Laplacian](../graph-laplacians-and-cheeger-s-inequality/laplacian.md) of the multigraph of darts of $G$ with conductance $c(d)/2$ on the dart $d$.

No positivity of $c$ is needed, since both sides are polynomials in the conductances. With $c \equiv 1$ the left side counts spanning trees, which gives the [matrix-tree theorem for principal minors of the Laplacian](../kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree-lap-matrix.md). For a disconnected graph both sides vanish.

## Background

- [Kirchhoff's matrix-tree theorem](../kirchhoff-s-matrix-tree-theorem/kirchhoff-matrix-tree.md): the unweighted theorem, proved.
