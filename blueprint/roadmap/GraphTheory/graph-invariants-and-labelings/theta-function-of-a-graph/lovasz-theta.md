# Lovász theta function

The Lovász number $\vartheta(G)$ of a graph $G$ on a vertex set $V$ is the infimum of the [feasible values](theta-feasible.md) of the theta program: the reals $t \ge 0$ for which there are a dimension $d$, an [orthogonal labeling](is-orthogonal-labeling.md) $a : V \to \mathbb{R}^d$ of $G$ (zero vectors allowed) and a nonzero handle $c \in \mathbb{R}^d$ with

$$
t \cdot \mathrm{cost}_c(a_v) \ge 1 \quad \text{for every } v \in V,
$$

the infimum of the empty set being read as $0$. A labeling meets this for some $t$ only if every vertex has positive cost, so for a finite graph with at least one vertex

$$
\vartheta(G) = \inf_{a,\,c} \ \max_{v} \frac{1}{\mathrm{cost}_c(a_v)},
$$

over the orthogonal labelings with positive cost at every vertex and the nonzero handles; Lovász shows that this infimum is attained. For a finite graph it is at least the independence number and at most the chromatic number of the complement ([sandwich theorem](sandwich.md)). The graph with no vertices has $\vartheta = 0$, every $t \ge 0$ being feasible.

This is the min-max form; Knuth defines $\vartheta(G)$ as $\max\{\mathbf 1 \cdot x : x \in \mathrm{TH}(G)\}$ and proves that the two agree (his eq. (5.1)).

## Sources

- L. Lovász, *On the Shannon capacity of a graph*, IEEE Trans. Inform. Theory 25 (1979), 1–7.
- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §4 and eq. (5.2) with unit weights.
