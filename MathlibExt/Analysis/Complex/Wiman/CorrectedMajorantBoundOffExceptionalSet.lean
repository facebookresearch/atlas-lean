/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Wiman.CorrectedRosenbloom
public import MathlibExt.Analysis.Complex.Wiman.TwoPowerBadSets

@[expose] public section

namespace Complex

open Filter MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **Majorant bound off an exceptional set.** Let $f$ be a transcendental entire function with
Taylor coefficients $a_n = f^{(n)}(0)/n!$, radial majorant $M_f(r) = \sum_n |a_n|\,|r|^n$, maximum
term $\mu_f(r) = \sup_n |a_n|\,|r|^n$ and logarithmic majorant $g_f(x) = \log M_f(e^x)$. There are
reals $C > 0$ and $x_0$ such that the Wiman exceptional set $E_f(x_0)$ has finite Lebesgue measure
and, for every real $x \ge x_0$ with $x \notin E_f(x_0)$,
$M_f(e^x) \le C\,\mu_f(e^x)\,\bigl(1 + g_f(x)^{81/128}\bigr)$. -/
theorem wimanMajorant_bound_off_exceptionalSet
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (htrans : IsTranscendental f) :
    ∃ C x₀ : ℝ, 0 < C ∧
      volume (wimanExceptionalSet f x₀) < ∞ ∧
      ∀ x, x₀ ≤ x → x ∉ wimanExceptionalSet f x₀ →
        wimanMajorant f (Real.exp x) ≤
          C * wimanMaximumTerm f (Real.exp x) *
            (1 + wimanGrowth f x ^ (81 / 128 : ℝ)) := by
  obtain ⟨xE, hEfinite, hEbound⟩ :=
    exists_finite_wimanExceptionalSet f hf htrans
  obtain ⟨xP, hpos, _, _, _, _⟩ := eventually_wimanGrowth_regular f hf htrans
  let x₀ : ℝ := max xE xP
  have hxE : xE ≤ x₀ := le_max_left _ _
  have hxP : xP ≤ x₀ := le_max_right _ _
  have hExceptionalSubset :
      wimanExceptionalSet f x₀ ⊆ wimanExceptionalSet f xE := by
    intro x hx
    simp only [wimanExceptionalSet, Real.powerGrowthBadSet, mem_union, mem_ofPred_eq] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl ⟨hxE.trans hx.1, hx.2⟩
    · exact Or.inr ⟨hxE.trans hx.1, hx.2⟩
  have hfinite : volume (wimanExceptionalSet f x₀) < ∞ :=
    measure_lt_top_mono hExceptionalSubset hEfinite
  refine ⟨8, x₀, by norm_num, hfinite, ?_⟩
  intro x hx hxgood
  have hxgoodE : x ∉ wimanExceptionalSet f xE := by
    intro hbad
    apply hxgood
    simp only [wimanExceptionalSet, Real.powerGrowthBadSet, mem_union, mem_ofPred_eq] at hbad ⊢
    rcases hbad with hbad | hbad
    · exact Or.inl ⟨hx, hbad.2⟩
    · exact Or.inr ⟨hx, hbad.2⟩
  have hsecond :
      iteratedDeriv 2 (wimanGrowth f) x ≤
        wimanGrowth f x ^ (81 / 64 : ℝ) :=
    hEbound x (hxE.trans hx) hxgoodE
  have hgx : 0 < wimanGrowth f x := hpos x (hxP.trans hx)
  have hsqrt :
      Real.sqrt (wimanGrowth f x ^ (81 / 64 : ℝ)) =
        wimanGrowth f x ^ (81 / 128 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hgx.le]
    congr 1
    norm_num
  have hmaximumNonneg : 0 ≤ wimanMaximumTerm f (Real.exp x) :=
    (wimanTerm_nonneg f (Real.exp x) 0).trans
      (wimanTerm_le_wimanMaximumTerm f hf (Real.exp x) 0)
  calc
    wimanMajorant f (Real.exp x) ≤
        8 * wimanMaximumTerm f (Real.exp x) *
          (1 + Real.sqrt (iteratedDeriv 2 (wimanGrowth f) x)) :=
      wimanMajorant_le_eight_mul_maximumTerm f hf x
    _ ≤ 8 * wimanMaximumTerm f (Real.exp x) *
          (1 + Real.sqrt (wimanGrowth f x ^ (81 / 64 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (Real.sqrt_le_sqrt hsecond) 1)
        (mul_nonneg (by norm_num) hmaximumNonneg)
    _ = 8 * wimanMaximumTerm f (Real.exp x) *
          (1 + wimanGrowth f x ^ (81 / 128 : ℝ)) := by
      rw [hsqrt]

end

end Complex
