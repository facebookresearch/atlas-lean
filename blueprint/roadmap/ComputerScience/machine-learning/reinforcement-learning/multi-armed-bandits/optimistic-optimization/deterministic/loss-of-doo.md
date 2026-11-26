# Loss of DOO

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](../hierarchical-partition.md) of a set $\mathcal X$ with
branching factor $K$, let $\ell$ be a [semi-metric](../semi-metric.md) on $\mathcal X$, and let
$f \colon \mathcal X \to \mathbb{R}$ be [locally smooth around a maximizer](../local-smoothness-around-a-maximizer.md)
$x^*$ with respect to $\ell$, with maximum $f^* = f(x^*)$. Let $\delta$
[bound the diameters of the cells](../bounded-diameters.md), let the cells be [well shaped](../well-shaped-cells.md)
for $\ell$ and $\delta$ with constant $\nu > 0$, and let $d \ge 0$ and $C > 0$ satisfy the
[$\nu$-near-optimality condition up to $\delta(0)$](../near-optimality-dimension.md) for $f$. For $n \in \mathbb{N}$,
let $h(n)$ be the smallest integer $h \ge 0$ such that

$$
C \sum_{l=0}^{h} \delta(l)^{-d} \ge n;
$$

it exists, since $0 < \delta(l) \le \delta(0)$ gives $\delta(l)^{-d} \ge \delta(0)^{-d} > 0$ for every $l$. Then every run
of [DOO](doo.md) with budget $n$ whose b-values use $\delta$ returns a point $x(n)$ whose
[loss](../loss.md) satisfies

$$
r_n = f^* - f(x(n)) \le \delta(h(n)).
$$

The bound is in terms of the number $n$ of expansions; DOO evaluates $f$ at $Kn + 1$ points (the sources count $Kn$,
leaving out the root).

## Proof

For every node $(h, i)$ whose cell contains $x^*$, local smoothness and the bound on the diameters give
$f(x_{h,i}) \ge f^* - \ell(x_{h,i}, x^*) \ge f^* - \delta(h)$, that is $b_{h,i} \ge f^*$ and $i \in I_h$, with $I_h$ as
in [the number of near-optimal cells](../number-of-near-optimal-cells.md). If $n = 0$, then $h(0) = 0$ and
$x(0) = x_{0,0}$, whose cell $\mathcal X$ contains $x^*$, so $r_0 \le \delta(0)$.

Let $n \ge 1$. Every exploration tree $T$ has a leaf whose cell contains $x^*$: start from the root, whose cell is
$\mathcal X$; while the current node is not a leaf, its children are in $T$ and exactly one of their cells contains
$x^*$, since they partition the current cell; go to that child; as $T$ is finite, this ends at a leaf. At step $t$
that leaf of $T_{t-1}$ has b-value at least $f^*$, so the leaf $(h, j)$ that DOO expands, of largest b-value,
satisfies $f(x_{h,j}) + \delta(h) \ge f^*$: $j \in I_h$. The $n$ expanded nodes are distinct, since an expanded node is
no longer a leaf. Let $h_{\max}$ be the largest depth of an expanded node and $(h_{\max}, j)$ such a node. For
$l \ge 0$ let $U_l = \{(l, i) : i \in I_l\}$, a finite set of nodes with $|U_l| \le |I_l|$, as $(l, i) \mapsto i$ maps it
injectively into $I_l$. By induction on $k$, $|U_0 \cup \dots \cup U_k| \le \sum_{l=0}^{k} |I_l|$, from
$|A \cup B| \le |A| + |B|$ and the values of a sum over $\{0, \dots, k\}$ for $k = 0$ and from $k$ to $k + 1$ (splitting
off the last term). The finite set of expanded nodes maps injectively (by the identity) into
$U_0 \cup \dots \cup U_{h_{\max}}$, so, comparing the sums term by term with the number of near-optimal cells at each
depth and taking the constant $C$ out of the sum, in $\mathbb{R}$,

$$
n \le \sum_{l=0}^{h_{\max}} |I_l| \le \sum_{l=0}^{h_{\max}} C \delta(l)^{-d} = C \sum_{l=0}^{h_{\max}} \delta(l)^{-d},
$$

and $h_{\max} \ge h(n)$ by the minimality of $h(n)$. As $(h_{\max}, j)$ is a node of $T_n$ and $\delta$ is
nonincreasing,

$$
f(x(n)) \ge f(x_{h_{\max}, j}) \ge f^* - \delta(h_{\max}) \ge f^* - \delta(h(n)).
$$

## Sources

- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.3.1, Theorem 3.2 and its proof, which the proof above follows,
  and Remark 3.4.
- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Theorem 1 and Remark 1.

## Depends on

- [Hierarchical partition](../hierarchical-partition.md)
- [Semi-metric](../semi-metric.md)
- [Local smoothness around a maximizer](../local-smoothness-around-a-maximizer.md)
- [Bounded diameters of the cells](../bounded-diameters.md)
- [Well-shaped cells](../well-shaped-cells.md)
- [Near-optimality dimension](../near-optimality-dimension.md)
- [Loss of a returned point](../loss.md)
- [Deterministic optimistic optimization (DOO)](doo.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
- [Real powers with a nonpositive exponent reverse the order](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-le-rpow-of-nonpos.md)
- [Real powers of a positive number are positive](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-pos-of-pos.md)
- [Every nonempty set of natural numbers has a least element](../../../../../../Order/ordered-sets/well-ordering-naturals.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)

## Proof depends on

- [Number of near-optimal cells at a given depth](../number-of-near-optimal-cells.md)
- [Counting through a map that is injective on a finite set](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-le-card-of-inj-on.md)
- [Cardinality of a union of two finite sets](../../../../../../SetTheory/finite-sets/cardinality-of-finite-sets/card-union-le.md)
- [Sum over the empty range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-zero.md)
- [Last term of a sum over a range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-succ.md)
- [Termwise comparison of finite sums](../../../../../../Algebra/big-operators/inequalities-for-finite-sums-and-products-in-ord/sum-le-sum.md)
- [Multiplying a finite sum by a constant](../../../../../../Algebra/big-operators/finite-sums-and-products-in-rings/mul-sum.md)
