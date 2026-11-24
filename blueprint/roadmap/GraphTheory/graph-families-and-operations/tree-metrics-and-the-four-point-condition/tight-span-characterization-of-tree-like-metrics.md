# Tree-like metrics and their tight spans

A metric space $X$ (writing $xy$ for the distance) is tree-like if it satisfies the four-point condition $xy + uv \le \sup(xu + yv,\ xv + yu)$ for all $x, y, u, v \in X$; for finite $X$, [Buneman's four-point theorem](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric-iff-four-point-condition.md) identifies these with the tree metrics. Dress (1984) extends this to arbitrary metric spaces through the tight span $T_X$, the set of functions $f : X \to \mathbb{R}$ with $f(x) = \sup_{y \in X}(xy - f(y))$ for all $x$, with the sup metric; equivalently, the minimal elements of $\{g : g(x) + g(y) \ge xy \text{ for all } x, y\}$, and $X$ embeds isometrically in $T_X$ by $x \mapsto (y \mapsto xy)$ (Theorem 3). His Theorem 8 states that the following are equivalent for any metric space $X$: $X$ is tree-like; $T_X$ is a tree (an $\mathbb{R}$-tree in the sense of conditions (T1)–(T2) of the source); the small inductive dimension of $T_X$ is $1$; and $X$ embeds isometrically into a tree. (The dimension condition presumes $|X| \ge 2$, since a one-point space has a one-point tight span.) Moreover, in this case every isometric embedding of $X$ into a tree $T$ extends uniquely to an isometric embedding of $T_X$ into $T$, so $T_X$ is the smallest tree containing $X$; and a metric space is a tree if and only if it is tree-like and connected, in which case its completion is $T_X$.

## Depends on

- [Buneman's four-point theorem](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric-iff-four-point-condition.md)

## Expansion

1. The tight span: Theorem 3 (the embedding $x \mapsto h_x$, the identity $\|h_x, f\| = f(x)$, and minimality in the set of functions dominating half the distances).
2. Universality and injectivity of the tight span (Sections 1.8–1.9).
3. The equivalence of the four-point condition with $T_X$ being an $\mathbb{R}$-tree, via the fact that $X$ is tree-like if and only if $T_X$ is (Section 4.1), and the reduction to Buneman's theorem for finite $X$.
4. The dimension conditions (iv)–(v) and the remaining conditions (iii) and (vi) of Theorem 8, as separate statements.
5. For finite $X$, the weighted tree realizing the metric and the [split decomposition of a tree metric](../../../Biology/phylogenetics/neighbor-joining/dist-eq-sum-darts.md).

## Sources

- A. W. M. Dress, Trees, tight extensions of metric spaces, and the cohomological dimension of certain groups: a note on combinatorial properties of metric spaces, Adv. Math. 53 (1984), 321–402, introduction, Theorems 3 and 8. <https://doi.org/10.1016/0001-8708(84)90029-x>
