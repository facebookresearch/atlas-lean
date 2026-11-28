# Loss of SOO for exponentially decreasing diameters

Assume the hypotheses of the [loss of SOO](loss-of-soo.md): a [hierarchical partition](../hierarchical-partition.md)
of $\mathcal X$, a [semi-metric](../semi-metric.md) $\ell$, a function $f$
[locally smooth around a maximizer](../local-smoothness-around-a-maximizer.md) with respect to $\ell$, with maximum
$f^*$, a function $\delta$ that [bounds the diameters of the cells](../bounded-diameters.md), cells
[well shaped](../well-shaped-cells.md) for $\ell$ and $\delta$ with constant $\nu > 0$, $d \ge 0$ and $C > 0$ that
satisfy the [$\nu$-near-optimality condition up to $\delta(0)$](../near-optimality-dimension.md) for $f$, and integers
$H \ge 1$ and $n \ge 1$. Assume moreover that $d > 0$ and that $\delta(h) = c \gamma^h$ for every $h \ge 0$, with
$c > 0$ and $0 < \gamma < 1$. Then every run of [SOO](soo.md) with budget $n$ and the constant depth function
$h_{\max}(t) = H$ has [loss](../loss.md) $r_n$ satisfying

$$
r_n \le \max\Big\{\Big(\frac{C}{1 - \gamma^d}\Big)^{1/d} \gamma^{-1} \Big(\frac{n}{H}\Big)^{-1/d}, \ c \gamma^{H}\Big\},
$$

where $\gamma^{-1} = 1/\gamma$, $\gamma^H$ is the $H$-th power of $\gamma$, and $\gamma^d$, $(\cdot)^{1/d}$ and
$(n/H)^{-1/d}$ are real powers. For a depth $H$ of order $(\log n)^a$ with $a > 1$, the first term is the larger one
for large $n$, and the bound is of order $n^{-1/d}$ up to a logarithmic factor. For $d = 0$, the bound of the
[loss of SOO](loss-of-soo.md) applies.

## Proof

Let $h = h(n)$, the smallest integer with $C H \sum_{l=0}^{h} \delta(l)^{-d} \ge n$. The loss of SOO gives
$r_n \le \delta(\min(h, H + 1)) = \max\{c \gamma^h, c \gamma^{H + 1}\}$, as $\delta$ is nonincreasing, and, as
$0 < \gamma < 1$, $\max\{c \gamma^h, c \gamma^{H + 1}\} \le \max\{\gamma^{-1} c \gamma^h, c \gamma^H\}$, which is
$\delta(\min(h - 1, H))$ when $h \ge 1$, the monograph's form.

Let $g = \gamma^d$, so $0 < g < 1$. As in the proof of the
[loss of DOO for exponentially decreasing diameters](loss-of-doo-for-exponentially-decreasing-diameters.md),
$\sum_{l=0}^{h} \delta(l)^{-d} = c^{-d} \sum_{l=0}^{h} g^{-l}$ and $\sum_{l=0}^{k} g^{-l} \le \frac{1}{(1 - g) g^k}$
for every $k$, so $n \le \frac{C H}{(1 - g) (c \gamma^h)^d}$, that is
$(c \gamma^h)^d \le \frac{C}{1 - g} \cdot \big(\frac{n}{H}\big)^{-1}$. Raising both sides to the power $1/d$ gives
$c \gamma^h \le \big(\frac{C}{1 - g}\big)^{1/d} \big(\frac{n}{H}\big)^{-1/d}$, as there; multiplying by
$\gamma^{-1} > 0$ bounds the first term.

## Sources

- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 4.1.1, Corollary 4.3 (case $d > 0$) and its proof, with the
  constant depth function $h_{\max} \equiv H$ (see the [loss of SOO](loss-of-soo.md) on depth functions that vary
  along the run).

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

## Proof depends on

- [Loss of SOO](loss-of-soo.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
- [Sum over the empty range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-zero.md)
- [Last term of a sum over a range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-succ.md)
- [Multiplying a finite sum by a constant](../../../../../../Algebra/big-operators/finite-sums-and-products-in-rings/mul-sum.md)
- [Real power with a natural exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-nat-cast.md)
- [Real power with exponent one](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-one.md)
- [Real power with a negated exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-neg.md)
- [Real power of a product](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/mul-rpow.md)
- [Real power with a product exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-mul.md)
- [Real powers of a positive number are positive](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-pos-of-pos.md)
- [Real powers below one](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-lt-one.md)
- [Monotonicity of real powers in the base](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-le-rpow.md)
