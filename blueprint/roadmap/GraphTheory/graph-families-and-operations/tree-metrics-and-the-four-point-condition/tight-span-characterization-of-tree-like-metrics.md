# Tree-like metrics and their tight spans

A metric space $X$ (writing $xy$ for the distance) is tree-like if its distance satisfies the [four-point condition](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/four-point-condition.md) $xy + uv \le \sup(xu + yv,\ xv + yu)$ for all $x, y, u, v \in X$; for finite $X$, [Buneman's four-point theorem](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric-iff-four-point-condition.md) identifies these with the tree metrics. Dress (1984) extends this to arbitrary metric spaces with at least two points: let $X$ be a metric space with $|X| \ge 2$, as Dress assumes from the start (Section 0, p. 321). Its tight span $T_X$ is the set of functions $f : X \to \mathbb{R}$ with $f(x) = \sup_{y \in X}(xy - f(y))$ for all $x$, with the sup metric; equivalently, the minimal elements of $\{g : g(x) + g(y) \ge xy \text{ for all } x, y\}$, and $X$ embeds isometrically in $T_X$ by $x \mapsto (y \mapsto xy)$ (Theorem 3). His Theorem 8 states that the following are equivalent for such $X$: $X$ is tree-like; $T_X$ is a tree (an $\mathbb{R}$-tree in the sense of conditions (T1)–(T2) of the source); the small inductive dimension of $T_X$ is $1$; and $X$ embeds isometrically into a tree. Moreover, in this case let $T_X^0 \subseteq T_X$ be the union of the segments of $T_X$ between the embedded points of $X$, a subtree; every isometric embedding of $X$ into a tree $T$ extends uniquely to an isometric embedding of $T_X^0$ into $T$, so $T_X^0$ is the smallest tree containing $X$ (Theorem 8 and Sections 4.8–4.10). The full tight span need not embed: for the tree $X = (0, 1)$, $T_X = [0, 1]$ admits no isometric embedding into $(0, 1)$ fixing $X$; the extension of the full tight span into a complete target tree is a separate target (Expansion item 4). Finally, a metric space $X$ with $|X| \ge 2$ is a tree if and only if it is tree-like and connected, in which case its completion is $T_X$. The remaining cases are separate: for a one-point space the four-point condition holds trivially and $T_X$ consists of the zero function alone, so $T_X^0 = T_X$ is a single point isometric to $X$ and has small inductive dimension $0$; for the empty space the four-point condition and the tree conditions hold vacuously, but its completion is empty while its tight span consists of the empty function, so the completion clause fails and the empty space is excluded.

## Depends on

- [Four-point condition](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/four-point-condition.md)

## Expansion

1. The tight span: Theorem 3 (the embedding $x \mapsto h_x$, the identity $\|h_x, f\| = f(x)$, and minimality in the set of functions dominating half the distances).
2. Universality and injectivity of the tight span (Sections 1.8–1.9).
3. The equivalence of the four-point condition with $T_X$ being an $\mathbb{R}$-tree, via the fact that $X$ is tree-like if and only if $T_X$ is (Section 4.1), and the reduction to Buneman's theorem for finite $X$.
4. The subtree $T_X^0$ spanned by $X$ and the unique extension of an embedding of $X$ into a tree (Sections 4.8–4.10); separately, whether $T_X$ embeds into every complete tree containing $X$, with the hypotheses under which a source states it.
5. The dimension conditions (iv)–(v) and the remaining conditions (iii) and (vi) of Theorem 8, as separate statements.
6. For finite $X$, the weighted tree realizing the metric and the [split decomposition of a tree metric](../../../Biology/phylogenetics/neighbor-joining/dist-eq-sum-darts.md).

## Sources

- A. W. M. Dress, Trees, tight extensions of metric spaces, and the cohomological dimension of certain groups: a note on combinatorial properties of metric spaces, Adv. Math. 53 (1984), 321–402, introduction, Theorems 3 and 8. <https://doi.org/10.1016/0001-8708(84)90029-x>
