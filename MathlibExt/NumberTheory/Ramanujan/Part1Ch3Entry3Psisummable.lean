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
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 3

Summability of the factorial series `∑ (-1)ʲ xʲ⁺¹ / ((z+1)⋯(z+j+1))` in a sector
`|arg z| ≤ π - ε`, derived from `Complex.summable_neg_pow_mul_pow_div_prod_add_mul`.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry3Psisummable

/-- **Summability of Ramanujan's factorial series in a sector, for every $x$.** Let $x$ be a
complex number and let $\varepsilon > 0$ be a real number. Then there is a real number $R$ such
that for every complex number $z$ with $|z| \ge R$ whose principal argument satisfies
$-\pi + \varepsilon \le \arg z \le \pi - \varepsilon$, the series
$\sum_{j=0}^{\infty} \frac{(-1)^j x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$ is summable. -/
theorem ramanujan_part1_ch3_entry3_psisummable_general (x : ℂ) (ε : ℝ) (hε₁ : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
      Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
          (z + (↑(k + 1) : ℂ))) := by
  refine ⟨0, fun z _ _ h => ?_⟩
  have hs := Complex.summable_neg_pow_mul_pow_div_prod_add_mul (b := 1) (c := z) x fun r hr => by
    have hz : z = ((-((r : ℝ) + 1) : ℝ) : ℂ) := by
      push_cast at hr ⊢
      linear_combination hr
    rw [hz, Complex.arg_ofReal_of_neg (neg_neg_of_pos (by positivity))] at h
    linarith
  simpa only [one_mul] using hs

set_option linter.unusedVariables false in
/-- **Summability of Ramanujan's factorial series in a sector.** Let $x$ be a nonzero complex
number and let $\varepsilon$ be a real number with $0 < \varepsilon < \pi$. Then there is a real
number $R$ such that for every complex number $z$ with $|z| \ge R$ whose principal argument
satisfies $-\pi + \varepsilon \le \arg z \le \pi - \varepsilon$, the series
$\sum_{j=0}^{\infty} \frac{(-1)^j x^{j+1}}{(z+1)(z+2)\cdots(z+j+1)}$ is summable.

The hypotheses $x \neq 0$ and $\varepsilon < \pi$ are not needed for the proof; they are kept to
match the source.

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Entry 3, printed p. 47 / PDF p.
    57.
Proves `Wanted` entry `ramanujan_part1_ch3_entry3_psisummable`. It follows from
`ramanujan_part1_ch3_entry3_psisummable_general`; the hypotheses `x ≠ 0` and `ε < π` are unused
and keep the source's shape.
-/
@[nolint unusedArguments]
theorem ramanujan_part1_ch3_entry3_psisummable (x : ℂ)
    (hx : x ≠ 0) (ε : ℝ) (hε₁ : 0 < ε) (hε₂ : ε < Real.pi) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → -Real.pi + ε ≤ Complex.arg z → Complex.arg z ≤ Real.pi - ε →
      Summable (fun j : ℕ => (-1 : ℂ) ^ j * x ^ (j + 1) / ∏ k ∈ Finset.range (j + 1),
          (z + (↑(k + 1) : ℂ))) :=
  ramanujan_part1_ch3_entry3_psisummable_general x ε hε₁

end Entry3Psisummable

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
