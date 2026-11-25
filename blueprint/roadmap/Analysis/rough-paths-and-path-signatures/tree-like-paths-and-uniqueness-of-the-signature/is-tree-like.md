# Tree-like path (Hambly–Lyons)

A path $X : [0, T] \to E$ in a normed group is tree-like if there is a continuous function
$h : [0, T] \to [0, \infty)$ with $h(0) = h(T) = 0$, a height function, such that

$$\| X_t - X_s \| \le h(s) + h(t) - 2 \inf_{u \in [s,t]} h(u) \qquad \text{for all } 0 \le s \le t \le T.$$

The right-hand side is the distance between the points at heights $h(s)$ and $h(t)$ in the
$\mathbb{R}$-tree coded by $h$, so a tree-like path factors through an $\mathbb{R}$-tree: it only
explores branches that it later retraces. Constant paths and a segment run out and back are
tree-like. The definition is meant for $T \ge 0$; for $T < 0$ the interval is empty and every path
qualifies.

## Sources

- B. Hambly and T. Lyons, *Uniqueness for the signature of a path of bounded variation and the
  reduced path group*, Ann. of Math. 171 (2010), arXiv:math/0507536, Definition 1.3 (a Lipschitz
  tree-like path is one with a height function of bounded variation).
