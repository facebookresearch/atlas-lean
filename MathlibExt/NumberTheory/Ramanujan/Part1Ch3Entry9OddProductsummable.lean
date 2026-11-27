/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import MathlibExt.Analysis.SpecificLimits.RisingProductSeries

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 9(i)

Summability of a partial-fraction-product series outside a sector, derived from
`Complex.summable_neg_pow_mul_pow_div_prod_add_mul`.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry9OddProductsummable

set_option linter.unusedVariables false in
/-- **Convergence of Ramanujan's product series in a sector.** Let $a, b, x \in \mathbb{C}$ with
$b \neq 0$ and let $0 < \varepsilon < \pi$. Then there is a real number $R$ such that for every
complex $z$ with $|(z + a)/b| \ge R$ and $-\pi + \varepsilon \le \arg((z + a)/b) \le
\pi - \varepsilon$, the series
$$\sum_{j=0}^{\infty} \frac{(-b)^j x^{j+1}}{\prod_{r=0}^{j} (z + a + b(r + 1))}$$
converges absolutely.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 9(i), definitions printed
    p. 53 / PDF p. 63 and result printed p. 54 / PDF p. 64.
It follows from `Complex.summable_neg_pow_mul_pow_div_prod_add_mul`: the upper sector bound keeps
`(z + a) / b` off the negative real axis, so no factor of the denominator vanishes. The hypothesis
`hεlt`, the radius (taken to be `0`) and the lower sector bound are unused and keep the source's
shape.
Proves `Wanted` entry `ramanujan_part1_ch3_entry9_odd_productsummable`.
-/
theorem ramanujan_part1_ch3_entry9_odd_productsummable (a b x : ℂ)
    (hb : b ≠ 0) (ε : ℝ) (hεpos : 0 < ε) (hεlt : ε < Real.pi) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖(z + a) / b‖ → -Real.pi + ε ≤ Complex.arg ((z + a) / b) →
        Complex.arg ((z + a) / b) ≤ Real.pi - ε →
            Summable (fun j : ℕ =>
                ((-b) ^ j * x ^ (j + 1) / ∏ r ∈ Finset.range (j + 1),
                    (z + a + b * ((r + 1 : ℕ) : ℂ)))) := by
  refine ⟨0, fun z _ _ h => Complex.summable_neg_pow_mul_pow_div_prod_add_mul x fun r hr => ?_⟩
  have hw : (z + a) / b = ((-((r : ℝ) + 1) : ℝ) : ℂ) := by
    rw [div_eq_iff hb]
    push_cast at hr ⊢
    linear_combination hr
  rw [hw, Complex.arg_ofReal_of_neg (neg_neg_of_pos (by positivity))] at h
  linarith

end Entry9OddProductsummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
