# Hierarchical optimistic optimization (HOO)

Let $(P_{h,i})$ be a [tree of coverings](tree-of-coverings.md) of a measurable space $\mathcal X$ whose regions are
all nonempty, as [geometrically shrinking regions](geometrically-shrinking-regions.md) ensure, and let
$\nu_1 > 0$ and $0 < \rho < 1$; the function to optimize is observed through [noisy evaluations](noisy-evaluations.md)
with rewards in $[0, 1]$. HOO plays one node per round and keeps the finite set $\mathcal T_n$ of nodes played in
rounds $1, \dots, n$ together with the root, starting from $\mathcal T_0 = \{(0, 1)\}$.

For a node $(h, i)$ and $n \ge 0$, let $T_{h,i}(n)$ be the number of rounds $t \le n$ whose node $(H_t, I_t)$ is a
descendant of $(h, i)$, and, when $T_{h,i}(n) \ge 1$, let $\hat\mu_{h,i}(n)$ be the average of the rewards of these
rounds. The *U-value* and the *B-value* of $(h, i)$ at the end of round $n$ are

$$
U_{h,i}(n) = \hat\mu_{h,i}(n) + \Big(\frac{2 \log n}{T_{h,i}(n)}\Big)^{1/2} + \nu_1 \rho^h
  \quad \text{if } T_{h,i}(n) \ge 1, \qquad U_{h,i}(n) = +\infty \quad \text{otherwise},
$$

$$
B_{h,i}(n) = \min\big\{U_{h,i}(n), \ \max\{B_{h+1, 2i-1}(n), B_{h+1, 2i}(n)\}\big\}
  \quad \text{if } (h, i) \in \mathcal T_n, \qquad B_{h,i}(n) = +\infty \quad \text{otherwise};
$$

Here the power $1/2$ and $\rho^h$ are real powers. As $\mathcal T_n$ is finite, the B-values are defined by induction
from the deepest nodes of $\mathcal T_n$ upward.

In round $n \ge 1$, HOO starts at the root and, as long as the current node belongs to $\mathcal T_{n-1}$, moves to its
child of larger B-value $B_{\cdot}(n - 1)$. The first node reached outside $\mathcal T_{n-1}$ is the node $(H_n, I_n)$
played in round $n$: HOO evaluates a point $X_n \in P_{H_n, I_n}$, receives the reward $Y_n$, and sets
$\mathcal T_n = \mathcal T_{n-1} \cup \{(H_n, I_n)\}$. Each node is played at most once, and every node of
$\mathcal T_n$ other than the root is a child of a node of $\mathcal T_n$. Ties between the two children are broken by
a fixed rule, such as the child $(h + 1, 2i - 1)$, and $X_n$ is drawn from a probability kernel of the past whose
values are concentrated on $P_{H_n, I_n}$ (for example a fixed point of each region). The
played nodes are then determined by the past rewards and points, and HOO is a strategy in the model of noisy
evaluations; results on HOO hold for every such rule. The source breaks ties at random and lets the choice of $X_n$ be
arbitrary; its analysis does not depend on these choices. The source states no nonemptiness condition for the tree,
but its algorithm chooses a point in the region of the node played, and its analysis assumes geometrically shrinking
regions, which are nonempty.

Along the path followed in a round the B-values do not decrease, since the B-value of a node of $\mathcal T_{n-1}$ is at
most the larger B-value of its children.

## Sources

- S. Bubeck, R. Munos, G. Stoltz and Cs. Szepesvári, *X-armed bandits*, Journal of Machine Learning Research 12
  (2011), 1655–1695, <https://jmlr.org/papers/v12/bubeck11a.html>, Section 3, Algorithm 1 and equation (3).
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.4.2, equation (3.12) and Figure 3.10.

## Depends on

- [Tree of coverings](tree-of-coverings.md)
- [Noisy evaluations](noisy-evaluations.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
- [Real logarithm](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-logarithm/log.md)
