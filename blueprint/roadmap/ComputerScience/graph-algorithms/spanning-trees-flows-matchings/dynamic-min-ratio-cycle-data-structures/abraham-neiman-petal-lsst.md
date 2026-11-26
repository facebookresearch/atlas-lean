# Abraham-Neiman low-stretch spanning trees via petal decompositions

Every connected $n$-vertex graph with $m$ edges and positive lengths $\boldsymbol{\ell}$ has a spanning tree $T$ with $\sum_{(u,v) \in E} d_T(u, v)/\boldsymbol{\ell}_{uv} = O(m\log n\log\log n)$, computable in $O(m\log n\log\log n)$ time. More generally, for any weights $\mathbf{v} \in \mathbb{R}^E_{>0}$ one can compute in $\widetilde{O}(m)$ time a $\gamma_{\mathrm{LSST}}$-low-stretch spanning tree with respect to $\mathbf{v}$ for

$$
\gamma_{\mathrm{LSST}} = O(\log n\log\log n).
$$

## Proof sketch

A petal decomposition splits a ball of radius $\Delta$ around a center into petals, each a ball in a suitably reweighted metric around a target point, so that each cluster has radius at most a constant factor times $\Delta$ and the probability that an edge of length $\ell$ is cut is $O(\ell\log n/\Delta)$ up to lower-order terms. Recursing on the petals and connecting them through their targets yields a spanning tree whose radius stays linear in $\Delta$ at every level, unlike star decompositions whose radius grows geometrically. Summing cut probabilities times radii over $O(\log n)$ scales, with a refined choice of cut radii, gives $O(\log n\log\log n)$ expected stretch per unit weight, and weights $\mathbf{v}$ enter by treating each edge as $\mathbf{v}_e$ parallel copies.

## Depends on

- [Edge stretch with respect to a spanning tree and edge lengths](edge-stretch-wrt-spanning-tree.md)

## Sources

- Ittai Abraham, Ofer Neiman, "Using Petal-Decompositions to Build a Low Stretch Spanning Tree", STOC (2012); SIAM J. Comput. 48(2) (2019).
- Michael Elkin, Yuval Emek, Daniel A. Spielman, Shang-Hua Teng, "Lower-Stretch Spanning Trees", STOC (2005), arXiv:cs/0411064.
