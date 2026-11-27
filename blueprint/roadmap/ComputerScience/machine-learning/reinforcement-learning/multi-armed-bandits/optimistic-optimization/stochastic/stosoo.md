# Stochastic simultaneous optimistic optimization (StoSOO)

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](../hierarchical-partition.md) of a measurable space
$\mathcal X$ with branching factor $K$, and let the function to optimize be observed through
[noisy evaluations](noisy-evaluations.md) with rewards in $[0, 1]$. StoSOO has four parameters: the number $k \ge 1$
of evaluations of a point before its node is expanded, the maximal depth $H \ge 0$, the budget $n$ (the number of
evaluations) and a confidence level $\delta \in (0, 1)$. Let $P_H$ be the finite set of the centers $x_{h,i}$ of the
nodes of depth $h \le H$, and $m_H = \lvert P_H \rvert$ its cardinality. The budget satisfies

$$
k + 1 \le n \le k\, m_H,
$$

a range that is empty unless $m_H \ge 2$, in particular when $H = 0$.

StoSOO keeps an [exploration tree](../exploration-trees.md) $T$ and evaluates only centers of its nodes. For a node
$(h, i)$, let $T_{h,i}$ be the number of evaluations made so far at the point $x_{h,i}$ and, when $T_{h,i} \ge 1$, let
$\hat\mu_{h,i}$ be the average of their rewards. The *b-value* of a node is

$$
b_{h,i} = \hat\mu_{h,i} + \Big(\frac{\log(nk/\delta)}{2 T_{h,i}}\Big)^{1/2} \quad \text{if } T_{h,i} \ge 1, \qquad
b_{h,i} = +\infty \quad \text{if } T_{h,i} = 0,
$$

where the power $1/2$ is a real power. StoSOO starts from $T = \{(0, 0)\}$ and $t = 1$, and repeats *sweeps* while
$t \le n$. A sweep does the following.

1. Set $v_{\max} = 0$ and $h_{\mathrm{top}} = \min(\operatorname{depth}(T), H)$, for the current $T$.
2. For $h = 0, 1, \dots, h_{\mathrm{top}}$, in this order, if $t \le n$ and $T$ has leaves of depth $h$: choose one,
   $(h, i)$, whose b-value is the largest among them. If $b_{h,i} \ge v_{\max}$, set $v_{\max} = b_{h,i}$; then, if
   $T_{h,i} < k$, evaluate the point $x_{h,i}$ and set $t = t + 1$, and otherwise expand $(h, i)$.

After $n$ evaluations, when $t = n + 1$, StoSOO returns the center $x(n)$ of an expanded node whose average
$\hat\mu_{h,j}$ is the largest among the expanded nodes. Ties are broken by a fixed rule, such as the smallest index,
so that StoSOO chooses each point from the past rewards: it is a deterministic strategy in the model of noisy
evaluations.

The bounds on $n$ make the run reach its output. For $p \in P_H$ let $T_p$ be the number of evaluations made at $p$.
Only points of $P_H$ are evaluated, each only while it has fewer than $k$ evaluations, so after $t - 1$ evaluations
$t - 1 = \sum_{p \in P_H} T_p \le \sum_{p \in P_H} k = k\, m_H$; beyond $k\, m_H$ the sweeps would go on forever.
Conversely, while $t \le n \le k\, m_H$, the sum $\sum_{p \in P_H} T_p = t - 1$ is less than $k\, m_H$, so some
$p \in P_H$ has $T_p < k$. No node with center $p$ has been expanded (expansion needs $k$ evaluations of its center),
so the tree has a leaf of depth at most $H$, and the sweep acts at the first depth $h \le h_{\mathrm{top}}$ that has
leaves, where the b-value chosen is positive, hence at least $v_{\max} = 0$. A sweep thus evaluates or expands; as each
of the finitely many nodes of depth at most $H$ is expanded at most once, the run makes its $n$ evaluations. The root,
the only leaf until it is expanded, is expanded before any $(k + 1)$-th evaluation, so $n \ge k + 1$ makes the returned
point defined.

This is the algorithm of the monograph's Figure 4.8 with the constant depth function $h_{\max}(t) = H$, the parameter
$\eta = n\delta/k$, for which its b-values (4.3), $\hat\mu + (\log(n^2/\eta)/(2T))^{1/2}$, are those above, and a
budget in the range above; the range of depths of a sweep is the bound of its loop, fixed when the sweep starts.
Algorithm 1 of the 2013 paper, which introduced StoSOO, uses the same b-values but differs in four points: it starts
from $t = 0$ and runs while $t \le n$, making $n + 1$ evaluations; it starts each sweep with $b_{\max} = -\infty$; it
updates $b_{\max}$ only when it expands a node; and it returns the node of largest average among the expanded nodes of
largest depth.

## Sources

- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 4.2, equation (4.3) and Figure 4.8, the algorithm stated above.
- M. Valko, A. Carpentier and R. Munos, *Stochastic simultaneous optimistic optimization*, Proceedings of the 30th
  International Conference on Machine Learning (ICML 2013), PMLR 28, <https://proceedings.mlr.press/v28/valko13.html>,
  Section 3.2, equation (4) and Algorithm 1, where StoSOO was introduced.

## Depends on

- [Hierarchical partition](../hierarchical-partition.md)
- [Exploration trees](../exploration-trees.md)
- [Noisy evaluations](noisy-evaluations.md)
- [Cardinality of a finite set](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
- [Real logarithm](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-logarithm/log.md)

## Proof depends on

- [Termwise comparison of finite sums](../../../../../../Algebra/big-operators/inequalities-for-finite-sums-and-products-in-ord/sum-le-sum.md)
