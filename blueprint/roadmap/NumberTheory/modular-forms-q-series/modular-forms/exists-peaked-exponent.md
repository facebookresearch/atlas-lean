# Peaked exponents for Siegel units

Let `2 ≤ N`. There are exponents
`m : ZMod N → ZMod N → ℕ` with `m 0 0 = 0` and `m r (s + r) = m r s` for all `r` and
`s`, whose Bernoulli order function
`Ord x y = ∑ r, ∑ s, m r s * (6 * v ^ 2 - 6 * N * v + N ^ 2)`, where `v` is the
representative in `[0, N)` of `r * x + s * y`, satisfies `0 < Ord 1 0` and
`Ord 1 0 < Ord x y` for every primitive pair `(x, y)` (one with `a * x + b * y = 1`
for some `a` and `b`) in the comparison set. So the vanishing order at `(1, 0)` is
positive and strictly smaller than at every pair of the comparison set.

The comparison set consists of the primitive pairs outside two exceptional families:

* the pairs with `y = 0` and `x = ±1`, that is `(1, 0)` itself and `(-1, 0)`, at which
  `Ord` takes the same value, because `Ord (-x) (-y) = Ord x y` (the weight
  `6 * v ^ 2 - 6 * N * v + N ^ 2` is unchanged under `v ↦ N - v`);
* the pairs with `y = ±1`, which the statement leaves out of the comparison.
