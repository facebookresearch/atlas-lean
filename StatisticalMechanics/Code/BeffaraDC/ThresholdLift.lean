/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.BeffaraDC.ActiveRussoHamming

open Set

namespace StatMech
namespace BeffaraDC



theorem thresholdLift_of_logisticDiffineq (f f' : ℝ → ℝ) {p₁ p₂ κ a : ℝ}
    (hp : p₁ ≤ p₂) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hf01 : ∀ p ∈ Icc p₁ p₂, f p ∈ Icc (0 : ℝ) 1)
    (hderiv : ∀ p ∈ Icc p₁ p₂, HasDerivAt f (f' p) p)
    (hdiff : ∀ p ∈ Icc p₁ p₂, κ * f p * (1 - f p) ≤ f' p)
    (hleft : a ≤ f p₁) :
    1 - Real.exp (-κ * a * (p₂ - p₁)) ≤ f p₂ := by
  have hfmono : MonotoneOn f (Icc p₁ p₂) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc p₁ p₂)
      (fun p hp' => (hderiv p hp').continuousAt.continuousWithinAt)
      (fun p hp' =>
        (hderiv p (interior_subset hp')).differentiableAt.differentiableWithinAt)
    intro p hp'
    rw [interior_Icc, mem_Ioo] at hp'
    have hmem : p ∈ Icc p₁ p₂ := ⟨hp'.1.le, hp'.2.le⟩
    rw [(hderiv p hmem).deriv]
    exact (mul_nonneg (mul_nonneg hκ (hf01 p hmem).1)
      (sub_nonneg.mpr (hf01 p hmem).2)).trans (hdiff p hmem)
  have hfa : ∀ p ∈ Icc p₁ p₂, a ≤ f p := by
    intro p hp'
    exact hleft.trans (hfmono (left_mem_Icc.mpr hp) hp' hp'.1)
  let u := fun p : ℝ => (1 - f p) * Real.exp (κ * a * p)
  have hu : AntitoneOn u (Icc p₁ p₂) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc p₁ p₂)
      (fun p hp' => (hderiv p hp').continuousAt.continuousWithinAt |>.const_sub 1 |>.mul
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousWithinAt))
      (fun p hp' => by
        have hf := (hderiv p (interior_subset hp')).const_sub 1
        have hlin : HasDerivAt (fun x : ℝ => κ * a * x) (κ * a) p := by
          simpa using (hasDerivAt_id p).const_mul (κ * a)
        exact (hf.mul ((Real.hasDerivAt_exp _).comp p hlin)).differentiableAt
          |>.differentiableWithinAt)
    intro p hp'
    rw [interior_Icc, mem_Ioo] at hp'
    have hmem : p ∈ Icc p₁ p₂ := ⟨hp'.1.le, hp'.2.le⟩
    change deriv u p ≤ 0
    have hlin : HasDerivAt (fun x : ℝ => κ * a * x) (κ * a) p := by
      simpa using (hasDerivAt_id p).const_mul (κ * a)
    have hexp := (Real.hasDerivAt_exp _).comp p hlin
    have hu' := ((hderiv p hmem).const_sub 1).mul hexp
    have huderiv : deriv u p =
        -f' p * Real.exp (κ * a * p) +
          (1 - f p) * (Real.exp (κ * a * p) * (κ * a)) := hu'.deriv
    rw [huderiv]
    have he : 0 < Real.exp (κ * a * p) := Real.exp_pos _
    have hmain : κ * a * (1 - f p) ≤ f' p := by
      have hclosed : 0 ≤ 1 - f p := sub_nonneg.mpr (hf01 p hmem).2
      have := mul_le_mul_of_nonneg_left (hfa p hmem) hκ
      have := mul_le_mul_of_nonneg_right this hclosed
      exact this.trans (hdiff p hmem)
    nlinarith
  have hend := hu (left_mem_Icc.mpr hp) (right_mem_Icc.mpr hp) hp
  change (1 - f p₂) * Real.exp (κ * a * p₂) ≤
    (1 - f p₁) * Real.exp (κ * a * p₁) at hend
  have hdeficit : 1 - f p₁ ≤ 1 := by linarith [(hf01 p₁ (left_mem_Icc.mpr hp)).1]
  have he₁ : 0 < Real.exp (κ * a * p₁) := Real.exp_pos _
  have he₂ : 0 < Real.exp (κ * a * p₂) := Real.exp_pos _
  have hend' : 1 - f p₂ ≤ Real.exp (κ * a * p₁) / Real.exp (κ * a * p₂) := by
    rw [le_div_iff₀ he₂]
    exact hend.trans (by simpa using mul_le_mul_of_nonneg_right hdeficit he₁.le)
  rw [← Real.exp_sub] at hend'
  have hexp : Real.exp (κ * a * p₁ - κ * a * p₂) =
      Real.exp (-κ * a * (p₂ - p₁)) := by ring_nf
  rw [hexp] at hend'
  linarith



theorem thresholdLift_logScale (f f' : ℝ → ℝ) {p₁ p₂ c a : ℝ} (n : ℕ)
    (hp : p₁ ≤ p₂) (hc : 0 ≤ c) (ha : 0 < a) (hn : 1 ≤ n)
    (hf01 : ∀ p ∈ Icc p₁ p₂, f p ∈ Icc (0 : ℝ) 1)
    (hderiv : ∀ p ∈ Icc p₁ p₂, HasDerivAt f (f' p) p)
    (hdiff : ∀ p ∈ Icc p₁ p₂,
      c * Real.log (n : ℝ) * f p * (1 - f p) ≤ f' p)
    (hleft : a ≤ f p₁) :
    1 - (n : ℝ) ^ (-c * a * (p₂ - p₁)) ≤ f p₂ := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnreal
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnreal
  have h := thresholdLift_of_logisticDiffineq f f' hp
    (mul_nonneg hc hlog) ha hf01 hderiv hdiff hleft
  rw [Real.rpow_def_of_pos hnpos]
  convert h using 1 <;> ring

end BeffaraDC
end StatMech
