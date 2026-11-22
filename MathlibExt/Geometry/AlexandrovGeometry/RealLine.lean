/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.AlexandrovGeometry.FourPointComparison
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Degenerate model angles and the real line

This file proves that straight degenerate model triangles have angle `π`,
that flat degenerate triangles have angle `0`, and that the real line is
`Alex κ` for every real `κ`.
-/

@[expose] public section

namespace AlexandrovGeometry

/-- The model angle opposite a straight side `b + c` is `π`. -/
theorem modelAngle_add_eq_pi (κ b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hdef : ModelTriangleDefined κ (b + c) b c) :
    modelAngle κ (b + c) b c = Real.pi := by
  by_cases h0 : κ = 0
  · subst h0
    rw [modelAngle_zero_left]
    apply Real.arccos_eq_pi.mpr
    have hden_ne : 2 * b * c ≠ 0 := ne_of_gt (mul_pos (mul_pos (by linarith) hb) hc)
    have harg : (b ^ 2 + c ^ 2 - (b + c) ^ 2) / (2 * b * c) = -1 := by
      rw [div_eq_iff hden_ne]; ring
    exact le_of_eq harg
  · have hne : κ ≠ 0 := h0
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have h0_false : κ ≠ 0 := ne_of_lt hneg
      rw [modelAngle_of_ne_zero h0_false]
      simp only [modelCos_of_neg hneg, modelSin_of_neg hneg]
      apply Real.arccos_eq_pi.mpr
      have hnk_pos : 0 < -κ := by linarith [hneg]
      have hs_pos : 0 < √(-κ) := Real.sqrt_pos.mpr hnk_pos
      have hs_ne : √(-κ) ≠ 0 := ne_of_gt hs_pos
      have hsinh_b : 0 < Real.sinh (√(-κ) * b) := Real.sinh_pos_iff.mpr (mul_pos hs_pos hb)
      have hsinh_c : 0 < Real.sinh (√(-κ) * c) := Real.sinh_pos_iff.mpr (mul_pos hs_pos hc)
      have hnegS_ne : -(Real.sinh (√(-κ) * b) * Real.sinh (√(-κ) * c)) ≠ 0 :=
        ne_of_lt (by linarith [mul_pos hsinh_b hsinh_c])
      have hs_sq : √(-κ) * √(-κ) = -κ := Real.mul_self_sqrt (le_of_lt hnk_pos)
      have hκ_eq : κ = -(√(-κ) * √(-κ)) := by linarith [hs_sq]
      have hden_eq : κ * (Real.sinh (√(-κ) * b) / √(-κ)) *
          (Real.sinh (√(-κ) * c) / √(-κ)) =
          -(Real.sinh (√(-κ) * b) * Real.sinh (√(-κ) * c)) := by
        nth_rewrite 1 [hκ_eq]
        field_simp
      have hnum_eq : Real.cosh (√(-κ) * (b + c)) -
          Real.cosh (√(-κ) * b) * Real.cosh (√(-κ) * c) =
          Real.sinh (√(-κ) * b) * Real.sinh (√(-κ) * c) := by
        have hadd : √(-κ) * (b + c) = √(-κ) * b + √(-κ) * c := by ring
        rw [hadd, Real.cosh_add]; ring
      have harg : (Real.cosh (√(-κ) * (b + c)) -
          Real.cosh (√(-κ) * b) * Real.cosh (√(-κ) * c)) /
          (κ * (Real.sinh (√(-κ) * b) / √(-κ)) *
            (Real.sinh (√(-κ) * c) / √(-κ))) = -1 := by
        rw [hnum_eq, hden_eq, div_eq_iff hnegS_ne]; ring
      exact le_of_eq harg
    · have hpos_lt : 0 < κ := hpos
      have h0_false : κ ≠ 0 := ne_of_gt hpos
      rw [modelAngle_of_ne_zero h0_false]
      simp only [modelCos_of_pos hpos_lt, modelSin_of_pos hpos_lt]
      apply Real.arccos_eq_pi.mpr
      have hs_pos : 0 < √κ := Real.sqrt_pos.mpr hpos_lt
      have hs_ne : √κ ≠ 0 := ne_of_gt hs_pos
      unfold ModelTriangleDefined at hdef
      have hper_lt : (b + c) + b + c < 2 * Real.pi / √κ := hdef.2.2.2 hpos_lt
      rw [show 2 * Real.pi / √κ = 2 * (Real.pi / √κ) from by ring] at hper_lt
      have hbc_lt : b + c < Real.pi / √κ := by linarith [hper_lt]
      have hb_lt : b < Real.pi / √κ := lt_of_le_of_lt (by linarith [hc]) hbc_lt
      have hc_lt : c < Real.pi / √κ := lt_of_le_of_lt (by linarith [hb]) hbc_lt
      have hsb_lt : √κ * b < Real.pi := by
        rw [mul_comm]; exact (lt_div_iff₀ hs_pos).mp hb_lt
      have hsc_lt : √κ * c < Real.pi := by
        rw [mul_comm]; exact (lt_div_iff₀ hs_pos).mp hc_lt
      have hsin_b : 0 < Real.sin (√κ * b) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos hs_pos hb) hsb_lt
      have hsin_c : 0 < Real.sin (√κ * c) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos hs_pos hc) hsc_lt
      have hS_ne : Real.sin (√κ * b) * Real.sin (√κ * c) ≠ 0 :=
        mul_ne_zero (ne_of_gt hsin_b) (ne_of_gt hsin_c)
      have hκ_eq : κ = √κ * √κ := (Real.mul_self_sqrt (le_of_lt hpos_lt)).symm
      have hden_eq : κ * (Real.sin (√κ * b) / √κ) *
          (Real.sin (√κ * c) / √κ) =
          Real.sin (√κ * b) * Real.sin (√κ * c) := by
        nth_rewrite 1 [hκ_eq]
        field_simp
      have hnum_eq : Real.cos (√κ * (b + c)) -
          Real.cos (√κ * b) * Real.cos (√κ * c) =
          -(Real.sin (√κ * b) * Real.sin (√κ * c)) := by
        have hadd : √κ * (b + c) = √κ * b + √κ * c := by ring
        rw [hadd, Real.cos_add]; ring
      have harg : (Real.cos (√κ * (b + c)) -
          Real.cos (√κ * b) * Real.cos (√κ * c)) /
          (κ * (Real.sin (√κ * b) / √κ) *
            (Real.sin (√κ * c) / √κ)) = -1 := by
        rw [hnum_eq, hden_eq, div_eq_iff hS_ne]; ring
      exact le_of_eq harg

/-- The model angle opposite a flat side `|b - c|` is `0`. -/
theorem modelAngle_abs_sub_eq_zero (κ b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hdef : ModelTriangleDefined κ |b - c| b c) :
    modelAngle κ |b - c| b c = 0 := by
  by_cases h0 : κ = 0
  · subst h0
    rw [modelAngle_zero_left]
    apply Real.arccos_eq_zero.mpr
    have hden_ne : 2 * b * c ≠ 0 := ne_of_gt (mul_pos (mul_pos (by linarith) hb) hc)
    have hsq : |b - c| ^ 2 = (b - c) ^ 2 := by
      rcases le_total 0 (b - c) with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h]; ring
    have harg : (b ^ 2 + c ^ 2 - |b - c| ^ 2) / (2 * b * c) = 1 := by
      rw [hsq, div_eq_iff hden_ne]; ring
    exact le_of_eq harg.symm
  · have hne : κ ≠ 0 := h0
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have h0_false : κ ≠ 0 := ne_of_lt hneg
      rw [modelAngle_of_ne_zero h0_false]
      simp only [modelCos_of_neg hneg, modelSin_of_neg hneg]
      apply Real.arccos_eq_zero.mpr
      have hnk_pos : 0 < -κ := by linarith [hneg]
      have hs_pos : 0 < √(-κ) := Real.sqrt_pos.mpr hnk_pos
      have hs_ne : √(-κ) ≠ 0 := ne_of_gt hs_pos
      have hsinh_b : 0 < Real.sinh (√(-κ) * b) := Real.sinh_pos_iff.mpr (mul_pos hs_pos hb)
      have hsinh_c : 0 < Real.sinh (√(-κ) * c) := Real.sinh_pos_iff.mpr (mul_pos hs_pos hc)
      have hnegS_ne : -(Real.sinh (√(-κ) * b) * Real.sinh (√(-κ) * c)) ≠ 0 :=
        ne_of_lt (by linarith [mul_pos hsinh_b hsinh_c])
      have hs_sq : √(-κ) * √(-κ) = -κ := Real.mul_self_sqrt (le_of_lt hnk_pos)
      have hκ_eq : κ = -(√(-κ) * √(-κ)) := by linarith [hs_sq]
      have hden_eq : κ * (Real.sinh (√(-κ) * b) / √(-κ)) *
          (Real.sinh (√(-κ) * c) / √(-κ)) =
          -(Real.sinh (√(-κ) * b) * Real.sinh (√(-κ) * c)) := by
        nth_rewrite 1 [hκ_eq]
        field_simp
      have hnum_eq : Real.cosh (√(-κ) * |b - c|) -
          Real.cosh (√(-κ) * b) * Real.cosh (√(-κ) * c) =
          -(Real.sinh (√(-κ) * b) * Real.sinh (√(-κ) * c)) := by
        rcases le_total b c with hbc | hcb
        · have habs : |b - c| = c - b := by
            rw [abs_of_nonpos (by linarith [hbc])]; ring
          have hmul : √(-κ) * |b - c| = √(-κ) * c - √(-κ) * b := by
            rw [habs]; ring
          rw [hmul, Real.cosh_sub]; ring
        · have habs : |b - c| = b - c := abs_of_nonneg (by linarith [hcb])
          have hmul : √(-κ) * |b - c| = √(-κ) * b - √(-κ) * c := by
            rw [habs]; ring
          rw [hmul, Real.cosh_sub]; ring
      have harg : (Real.cosh (√(-κ) * |b - c|) -
          Real.cosh (√(-κ) * b) * Real.cosh (√(-κ) * c)) /
          (κ * (Real.sinh (√(-κ) * b) / √(-κ)) *
            (Real.sinh (√(-κ) * c) / √(-κ))) = 1 := by
        rw [hnum_eq, hden_eq]; exact div_self hnegS_ne
      exact le_of_eq harg.symm
    · have hpos_lt : 0 < κ := hpos
      have h0_false : κ ≠ 0 := ne_of_gt hpos
      rw [modelAngle_of_ne_zero h0_false]
      simp only [modelCos_of_pos hpos_lt, modelSin_of_pos hpos_lt]
      apply Real.arccos_eq_zero.mpr
      have hs_pos : 0 < √κ := Real.sqrt_pos.mpr hpos_lt
      have hs_ne : √κ ≠ 0 := ne_of_gt hs_pos
      unfold ModelTriangleDefined at hdef
      have hper_lt : |b - c| + b + c < 2 * Real.pi / √κ := hdef.2.2.2 hpos_lt
      rw [show 2 * Real.pi / √κ = 2 * (Real.pi / √κ) from by ring] at hper_lt
      have hbounds : b < Real.pi / √κ ∧ c < Real.pi / √κ := by
        rcases le_total b c with hbc | hcb
        · have habs : |b - c| = c - b := by
            rw [abs_of_nonpos (by linarith [hbc])]; ring
          have hc_lt : c < Real.pi / √κ := by linarith [hper_lt, habs]
          exact ⟨lt_of_le_of_lt hbc hc_lt, hc_lt⟩
        · have habs : |b - c| = b - c := abs_of_nonneg (by linarith [hcb])
          have hb_lt : b < Real.pi / √κ := by linarith [hper_lt, habs]
          exact ⟨hb_lt, lt_of_le_of_lt hcb hb_lt⟩
      have hb_lt : b < Real.pi / √κ := hbounds.1
      have hc_lt : c < Real.pi / √κ := hbounds.2
      have hsb_lt : √κ * b < Real.pi := by
        rw [mul_comm]; exact (lt_div_iff₀ hs_pos).mp hb_lt
      have hsc_lt : √κ * c < Real.pi := by
        rw [mul_comm]; exact (lt_div_iff₀ hs_pos).mp hc_lt
      have hsin_b : 0 < Real.sin (√κ * b) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos hs_pos hb) hsb_lt
      have hsin_c : 0 < Real.sin (√κ * c) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos hs_pos hc) hsc_lt
      have hS_ne : Real.sin (√κ * b) * Real.sin (√κ * c) ≠ 0 :=
        mul_ne_zero (ne_of_gt hsin_b) (ne_of_gt hsin_c)
      have hκ_eq : κ = √κ * √κ := (Real.mul_self_sqrt (le_of_lt hpos_lt)).symm
      have hden_eq : κ * (Real.sin (√κ * b) / √κ) *
          (Real.sin (√κ * c) / √κ) =
          Real.sin (√κ * b) * Real.sin (√κ * c) := by
        nth_rewrite 1 [hκ_eq]
        field_simp
      have hnum_eq : Real.cos (√κ * |b - c|) -
          Real.cos (√κ * b) * Real.cos (√κ * c) =
          Real.sin (√κ * b) * Real.sin (√κ * c) := by
        rcases le_total b c with hbc | hcb
        · have habs : |b - c| = c - b := by
            rw [abs_of_nonpos (by linarith [hbc])]; ring
          have hmul : √κ * |b - c| = √κ * c - √κ * b := by
            rw [habs]; ring
          rw [hmul, Real.cos_sub]; ring
        · have habs : |b - c| = b - c := abs_of_nonneg (by linarith [hcb])
          have hmul : √κ * |b - c| = √κ * b - √κ * c := by
            rw [habs]; ring
          rw [hmul, Real.cos_sub]; ring
      have harg : (Real.cos (√κ * |b - c|) -
          Real.cos (√κ * b) * Real.cos (√κ * c)) /
          (κ * (Real.sin (√κ * b) / √κ) *
            (Real.sin (√κ * c) / √κ)) = 1 := by
        rw [hnum_eq, hden_eq]; exact div_self hS_ne
      exact le_of_eq harg.symm

/-- The real line is `Alex κ` for every real `κ`. -/
theorem isAlex_real (κ : ℝ) : IsAlex κ ℝ := by
  unfold IsAlex FourPointComparison
  intro p x₁ x₂ x₃ hdef
  unfold ModelAngleDefined at hdef
  have htri12 : ModelTriangleDefined κ (dist x₁ x₂) (dist p x₁) (dist p x₂) := hdef.1.1
  have hp1 : 0 < dist p x₁ := hdef.1.2.1
  have hp2 : 0 < dist p x₂ := hdef.1.2.2
  have htri23 : ModelTriangleDefined κ (dist x₂ x₃) (dist p x₂) (dist p x₃) := hdef.2.1.1
  have hp3 : 0 < dist p x₃ := hdef.2.1.2.2
  have htri31 : ModelTriangleDefined κ (dist x₃ x₁) (dist p x₃) (dist p x₁) := hdef.2.2.1
  have hle12 : comparisonAngle κ p x₁ x₂ ≤ Real.pi := by
    unfold comparisonAngle; exact modelAngle_le_pi _ _ _ _
  have hle23 : comparisonAngle κ p x₂ x₃ ≤ Real.pi := by
    unfold comparisonAngle; exact modelAngle_le_pi _ _ _ _
  have hle31 : comparisonAngle κ p x₃ x₁ ≤ Real.pi := by
    unfold comparisonAngle; exact modelAngle_le_pi _ _ _ _
  have hzero_of_same : ∀ {x y : ℝ}, ((x < p ∧ y < p) ∨ (p < x ∧ p < y)) →
      ModelTriangleDefined κ (dist x y) (dist p x) (dist p y) →
      0 < dist p x → 0 < dist p y → comparisonAngle κ p x y = 0 := by
    intro x y hside htri hpx hpy
    rcases hside with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hpx_eq : |p - x| = p - x := abs_of_nonneg (by linarith [hx])
      have hpy_eq : |p - y| = p - y := abs_of_nonneg (by linarith [hy])
      have hxy_eq : x - y = (p - y) - (p - x) := by ring
      have hdist_eq : dist x y = |dist p x - dist p y| := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, hxy_eq, hpx_eq, hpy_eq]
        exact abs_sub_comm _ _
      rw [hdist_eq] at htri
      unfold comparisonAngle
      rw [hdist_eq]
      exact modelAngle_abs_sub_eq_zero κ _ _ hpx hpy htri
    · have hpx_eq : |p - x| = x - p := by
        rw [abs_of_nonpos (by linarith [hx])]; ring
      have hpy_eq : |p - y| = y - p := by
        rw [abs_of_nonpos (by linarith [hy])]; ring
      have hxy_eq : x - y = (x - p) - (y - p) := by ring
      have hdist_eq : dist x y = |dist p x - dist p y| := by
        rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, hxy_eq, hpx_eq, hpy_eq]
      rw [hdist_eq] at htri
      unfold comparisonAngle
      rw [hdist_eq]
      exact modelAngle_abs_sub_eq_zero κ _ _ hpx hpy htri
  have hside : ∀ {x : ℝ}, 0 < dist p x → x < p ∨ p < x := by
    intro x hpx
    have hpx' : 0 < |p - x| := by simpa [Real.dist_eq] using hpx
    have hsub_ne : p - x ≠ 0 := abs_pos.mp hpx'
    exact lt_or_gt_of_ne (fun heq => hsub_ne (by rw [heq, sub_self]))
  have hside1 : x₁ < p ∨ p < x₁ := hside hp1
  have hside2 : x₂ < p ∨ p < x₂ := hside hp2
  have hside3 : x₃ < p ∨ p < x₃ := hside hp3
  rcases hside1 with h1 | h1
  · rcases hside2 with h2 | h2
    · have hz12 : comparisonAngle κ p x₁ x₂ = 0 := hzero_of_same (Or.inl ⟨h1, h2⟩) htri12 hp1 hp2
      rw [hz12]; linarith [hle23, hle31]
    · rcases hside3 with h3 | h3
      · have hz31 : comparisonAngle κ p x₃ x₁ = 0 :=
          hzero_of_same (Or.inl ⟨h3, h1⟩) htri31 hp3 hp1
        rw [hz31]; linarith [hle12, hle23]
      · have hz23 : comparisonAngle κ p x₂ x₃ = 0 :=
          hzero_of_same (Or.inr ⟨h2, h3⟩) htri23 hp2 hp3
        rw [hz23]; linarith [hle12, hle31]
  · rcases hside2 with h2 | h2
    · rcases hside3 with h3 | h3
      · have hz23 : comparisonAngle κ p x₂ x₃ = 0 :=
          hzero_of_same (Or.inl ⟨h2, h3⟩) htri23 hp2 hp3
        rw [hz23]; linarith [hle12, hle31]
      · have hz31 : comparisonAngle κ p x₃ x₁ = 0 :=
          hzero_of_same (Or.inr ⟨h3, h1⟩) htri31 hp3 hp1
        rw [hz31]; linarith [hle12, hle23]
    · have hz12 : comparisonAngle κ p x₁ x₂ = 0 := hzero_of_same (Or.inr ⟨h1, h2⟩) htri12 hp1 hp2
      rw [hz12]; linarith [hle23, hle31]

end AlexandrovGeometry
