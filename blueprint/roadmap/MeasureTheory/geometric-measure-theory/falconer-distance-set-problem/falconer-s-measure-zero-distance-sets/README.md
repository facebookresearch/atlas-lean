# Falconer's measure-zero distance set examples

For every integer $d \ge 2$ and every $s$ with $0 \le s \le d/2$, there is a compact set
$E \subseteq \mathbb{R}^d$ of Hausdorff dimension exactly $s$ whose distance set
$\{|x - y| : x, y \in E\}$ has one-dimensional Lebesgue measure zero.

## Idea

These examples show that dimension $d/2$ does not suffice, so the critical exponent of the problem
lies between $d/2$ and Falconer's $(d+1)/2$. The sets are built from small neighbourhoods of the
points of scaled integer lattices, at a rapidly growing sequence of scales: lattice points
determine few distinct distances, which keeps the distance set small at every scale. In the plane they give the lower bound
$1$ for the threshold: a compact set of dimension $t$ whose distance set is null shows that no
number below $t$ is a threshold.

## Statements

- [Falconer's measure-zero distance set examples](falconer1985-lattice-examples-holds.md)
- [Statement of Falconer's measure-zero distance set examples](falconer1985-lattice-examples.md): the statement as a proposition.
- [Zero-measure distance sets give lower bounds for the planar distance threshold](le-planar-distance-threshold-of-zero-mea.md): turns such an example into a lower bound for the threshold.
- [Falconer's lower bound for the planar distance threshold](lower-bound-falconer1985-holds.md): a consequence, the threshold is at least $1$.
- [Statement of the lower bound $1$ for the planar distance threshold](lower-bound-falconer1985.md): that bound as a proposition.

## Background

- [Planar Falconer distance threshold](../planar-falconer-threshold/README.md)

## Sources

- L. Guth, A. Iosevich, Y. Ou and H. Wang, arXiv:1808.09346v1, introduction, a secondary source reporting Falconer (1985).
