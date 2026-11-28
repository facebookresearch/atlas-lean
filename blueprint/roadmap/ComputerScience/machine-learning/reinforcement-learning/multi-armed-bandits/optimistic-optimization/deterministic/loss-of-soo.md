# Loss of SOO

Let $(X_{h,i}, x_{h,i})$ be a [hierarchical partition](../hierarchical-partition.md) of a set $\mathcal X$ with
branching factor $K$, let $\ell$ be a [semi-metric](../semi-metric.md) on $\mathcal X$, and let
$f \colon \mathcal X \to \mathbb{R}$ be [locally smooth around a maximizer](../local-smoothness-around-a-maximizer.md)
$x^*$ with respect to $\ell$, with maximum $f^* = f(x^*)$. Let $\delta$
[bound the diameters of the cells](../bounded-diameters.md), let the cells be [well shaped](../well-shaped-cells.md) for
$\ell$ and $\delta$ with constant $\nu > 0$, and let $d \ge 0$ and $C > 0$ satisfy the
[$\nu$-near-optimality condition up to $\delta(0)$](../near-optimality-dimension.md) for $f$. Let $H \ge 1$ and
$n \ge 1$ be integers, and let $h(n)$ be the smallest integer $h \ge 0$ such that

$$
C H \sum_{l=0}^{h} \delta(l)^{-d} \ge n;
$$

it exists, since $0 < \delta(l) \le \delta(0)$ gives $\delta(l)^{-d} \ge \delta(0)^{-d} > 0$ for every $l$. Then every run
of [SOO](soo.md) with budget $n$ and the constant depth function $h_{\max}(t) = H$ returns a point $x(n)$ whose
[loss](../loss.md) satisfies

$$
r_n = f^* - f(x(n)) \le \delta\big(\min(h(n), H + 1)\big).
$$

SOO uses neither $\ell$ nor $\delta$, so the bound holds at once for every semi-metric $\ell$ and every
$\delta$, $\nu$, $d$ and $C$ that satisfy the hypotheses, the best of which need not be known. The depth $H$
appears twice: as a factor in the definition of $h(n)$ and as a threshold in the bound, a trade-off between deep and
broad exploration. As $\delta$ is nonincreasing, the bound implies
$r_n \le \delta\big(\min(h(n) - 1, H)\big)$ when $h(n) \ge 1$, the form of the monograph's Theorem 4.2.

The sources state the bound for a depth function $t \mapsto h_{\max}(t)$, with $h_{\max}(n)$ in place of $H$; with a
depth function that varies along the run, the bound can fail. On $\mathcal X = [0, 1)$ with $K = 100$, the $100$-adic
cells and their midpoints, $\ell(x, y) = |x - y|$ and $f(x) = 1 - |x - 3/10|$ (so that $\delta(h) = K^{-h}/2$,
$\nu = 1$, $d = 0$ and $C = 2$ satisfy the hypotheses), the depth function with $h_{\max}(t) = 1$ for $t < 49$ and
$h_{\max}(t) = 5$ for $t \ge 49$ and the budget $n = 49$ give $r_{49} \ge \delta(2)$, whereas the bound with
$h_{\max}(49) = 5$ in place of $H$ gives $\delta(4)$.

## Proof

For every node $(h, i)$ whose cell contains $x^*$, local smoothness and the bound on the diameters give
$f(x_{h,i}) \ge f^* - \ell(x_{h,i}, x^*) \ge f^* - \delta(h)$. If $h(n) = 0$, the root is a node of the final tree, so
$r_n \le f^* - f(x_{0,0}) \le \delta(0)$.

Let $h(n) \ge 1$, $h' = \min(h(n) - 1, H)$ and $I_l$ as in
[the number of near-optimal cells](../number-of-near-optimal-cells.md). Comparing the sums term by term with that
bound, taking the constant $C$ out of the sum, and using the minimality of $h(n)$ at $h' < h(n)$, in $\mathbb{R}$,

$$
H \sum_{l=0}^{h'} |I_l| \le H \sum_{l=0}^{h'} C \delta(l)^{-d} = C H \sum_{l=0}^{h'} \delta(l)^{-d} < n,
$$

so the depth reached by SOO, with $t = n$ and $h = h' \le H$, gives $h^*_n \ge h'$. Let $(h^*_n, i)$ be the deepest
expanded node whose cell contains $x^*$. One of its children, $(h^*_n + 1, i')$, has a cell that contains $x^*$, and it
is a node of the final tree, so

$$
f(x(n)) \ge f(x_{h^*_n + 1, i'}) \ge f^* - \delta(h^*_n + 1) \ge f^* - \delta(h' + 1) = f^* - \delta\big(\min(h(n), H + 1)\big),
$$

as $\delta$ is nonincreasing.

## Sources

- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Theorem 2 and Remark 2; the bound above is that of
  Theorem 2, with a constant depth function.
- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 4.1.1, Theorem 4.2 and its proof, which the proof above follows,
  except that it bounds the loss through the evaluated child of the deepest expanded node containing $x^*$.

## Depends on

- [Hierarchical partition](../hierarchical-partition.md)
- [Semi-metric](../semi-metric.md)
- [Local smoothness around a maximizer](../local-smoothness-around-a-maximizer.md)
- [Bounded diameters of the cells](../bounded-diameters.md)
- [Well-shaped cells](../well-shaped-cells.md)
- [Near-optimality dimension](../near-optimality-dimension.md)
- [Loss of a returned point](../loss.md)
- [Simultaneous optimistic optimization (SOO)](soo.md)
- [Real power of a real number](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow.md)
- [Real powers with a nonpositive exponent reverse the order](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-le-rpow-of-nonpos.md)
- [Real powers of a positive number are positive](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-pos-of-pos.md)
- [Every nonempty set of natural numbers has a least element](../../../../../../Order/ordered-sets/well-ordering-naturals.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)

## Proof depends on

- [Depth reached by SOO along an optimal branch](depth-reached-by-soo.md)
- [Number of near-optimal cells at a given depth](../number-of-near-optimal-cells.md)
- [Termwise comparison of finite sums](../../../../../../Algebra/big-operators/inequalities-for-finite-sums-and-products-in-ord/sum-le-sum.md)
- [Multiplying a finite sum by a constant](../../../../../../Algebra/big-operators/finite-sums-and-products-in-rings/mul-sum.md)
