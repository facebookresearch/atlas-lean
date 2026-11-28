# Loss of DOO for exponentially decreasing diameters

Assume the hypotheses of the [loss of DOO](loss-of-doo.md): a [hierarchical partition](../hierarchical-partition.md)
of $\mathcal X$, a [semi-metric](../semi-metric.md) $\ell$, a function $f$
[locally smooth around a maximizer](../local-smoothness-around-a-maximizer.md) with respect to $\ell$, with maximum
$f^*$, a function $\delta$ that [bounds the diameters of the cells](../bounded-diameters.md), cells
[well shaped](../well-shaped-cells.md) for $\ell$ and $\delta$ with constant $\nu > 0$, and $d \ge 0$, $C > 0$ that
satisfy the [$\nu$-near-optimality condition up to $\delta(0)$](../near-optimality-dimension.md) for $f$. Assume
moreover that $\delta(h) = c \gamma^h$ for every $h \ge 0$, with $c > 0$ and $0 < \gamma < 1$. Then every run of
[DOO](doo.md) with budget $n$ whose b-values use $\delta$ has [loss](../loss.md) $r_n$ satisfying:

- if $d > 0$ and $n \ge 1$,

    $$
    r_n \le \Big(\frac{C}{1 - \gamma^d}\Big)^{1/d} n^{-1/d};
    $$

- if $d = 0$,

    $$
    r_n \le c \gamma^{n/C - 1}.
    $$

The powers $\gamma^d$, $(\cdot)^{1/d}$, $n^{-1/d}$ and $\gamma^{n/C - 1}$ are real powers. The loss decreases
polynomially in $n$ when $d > 0$ and exponentially when $d = 0$.

## Proof

Let $h = h(n)$, the smallest integer with $C \sum_{l=0}^{h} \delta(l)^{-d} \ge n$. The loss of DOO gives
$r_n \le \delta(h) = c \gamma^h$.

If $d = 0$, then $\delta(l)^{-0} = 1$ for every $l$, and $\sum_{l=0}^{h} 1 = h + 1$ by induction on $h$ (the sum over
$\{0, \dots, k\}$ for $k = 0$ and from $k$ to $k + 1$, splitting off the last term), so $C (h + 1) \ge n$ and
$h \ge n/C - 1$. With $\gamma^h = \gamma^{(h : \mathbb{R})}$ and $0 < \gamma \le 1$, $\gamma^h \le \gamma^{n/C - 1}$.

Let $d > 0$ and $g = \gamma^d$, so $0 < g < 1$. For every $l$, $(\gamma^l)^d = \gamma^{l d} = (\gamma^d)^l = g^l$
(writing $\gamma^l = \gamma^{(l : \mathbb{R})}$ and using $x^{yz} = (x^y)^z$ twice) and
$(c \gamma^l)^d = c^d g^l$, so $\delta(l)^{-d} = \big(c^d g^l\big)^{-1} = c^{-d} \cdot \frac{1}{g^l}$ and, taking the
constant out of the sum, $\sum_{l=0}^{h} \delta(l)^{-d} = c^{-d} \sum_{l=0}^{h} \frac{1}{g^l}$. By induction on $k$,
with the same values of a sum over $\{0, \dots, k\}$,

$$
\sum_{l=0}^{k} \frac{1}{g^l} \le \frac{1}{(1 - g) g^k},
$$

as $1 \le \frac{1}{1 - g}$ and $\frac{1}{(1 - g) g^k} + \frac{1}{g^{k+1}} = \frac{1}{(1 - g) g^{k+1}}$. Hence
$n \le C c^{-d} \sum_{l=0}^{h} \frac{1}{g^l} \le \frac{C}{c^d (1 - g) g^h} = \frac{C}{(1 - g) (c \gamma^h)^d}$, that is
$(c \gamma^h)^d \le \frac{C}{(1 - g) n}$, a bound between positive reals. Raising both sides to the power $1/d \ge 0$
and using $\big((c \gamma^h)^d\big)^{1/d} = (c \gamma^h)^{d \cdot (1/d)} = c \gamma^h$,

$$
c \gamma^h \le \Big(\frac{C}{1 - g} \cdot n^{-1}\Big)^{1/d} = \Big(\frac{C}{1 - g}\Big)^{1/d} \big(n^{-1}\big)^{1/d}
  = \Big(\frac{C}{1 - g}\Big)^{1/d} n^{-1/d},
$$

where $n^{-1} = n^{(-1)}$ is a real power and $(n^{(-1)})^{1/d} = n^{-1/d}$.

## Sources

- R. Munos, *From Bandits to Monte-Carlo Tree Search: The Optimistic Principle Applied to Optimization and Planning*,
  Foundations and Trends in Machine Learning 7(1), 2014, 1–129 (HAL hal-00747575v5,
  <https://hal.science/hal-00747575v5>), Section 3.3.1, Corollary 3.3 and its proof.
- R. Munos, *Optimistic optimization of a deterministic function without the knowledge of its smoothness*, Advances
  in Neural Information Processing Systems 24 (NeurIPS 2011), Corollary 1. Its constant for $d > 0$,
  $c^{(d+1)/d} (1 - \gamma^d)^{-1/d} C^{1/d}$, does not hold in general: replacing $f$ and $\ell$ by $\lambda f$ and
  $\lambda \ell$ keeps the hypotheses (with $c$, $C$ and $\delta(0)$ rescaled) and the choices of DOO, and multiplies the
  loss by $\lambda$ but that bound by $\lambda^{2 + 1/d}$. The bound above uses the constant of the monograph's
  Corollary 3.3.

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

## Proof depends on

- [Loss of DOO](loss-of-doo.md)
- [Sum over a finite set](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum.md)
- [Sum over the empty range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-zero.md)
- [Last term of a sum over a range](../../../../../../Algebra/big-operators/sums-and-products-over-finite-sets/sum-range-succ.md)
- [Multiplying a finite sum by a constant](../../../../../../Algebra/big-operators/finite-sums-and-products-in-rings/mul-sum.md)
- [Real power with exponent zero](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-zero.md)
- [Real power with a natural exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-nat-cast.md)
- [Real power with exponent one](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-one.md)
- [Real power with a negated exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-neg.md)
- [Real power of a product](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/mul-rpow.md)
- [Real power with a product exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-mul.md)
- [Real powers of a positive number are positive](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-pos-of-pos.md)
- [Real powers below one](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-lt-one.md)
- [Monotonicity of real powers in the base](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-le-rpow.md)
- [Real powers of a base at most one decrease with the exponent](../../../../../../Analysis/special-functions/elementary-transcendental-functions/real-powers/rpow-le-rpow-of-exponent-ge.md)
