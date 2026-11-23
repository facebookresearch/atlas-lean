/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerODE
public import Mathlib

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.LoewnerODE`

* `loewnerStrip`, `loewnerField_norm_le` (attained: `‖2 / I‖ = 2`), `loewnerField_lipschitzOnWith`
  for `W = 0`, `δ = 1`.
* `isPicardLindelof_loewnerField` and its consequences `exists_isLoewnerSolutionOn_Icc`,
  `exists_isLoewnerSolution_hasDerivAt`, `exists_isLoewnerSolutionOn`,
  `exists_unique_loewnerSolution` with `W = 0`, `z₀ = I`, `t₀ = 0`.
* `loewnerSolution_unique_Ioo`: any solution through `I` staying in `{Im ≥ 1/2}` on
  `(-1/8, 1/8)` equals the explicit solution `I √(1 - 4t)`.
-/

@[expose] public section

open StatMech.SLE Complex Set
open UpperHalfPlane (upperHalfPlaneSet)

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerODE

/-- The explicit Loewner trajectory of `z = I` for `W = 0`: `g_t(I) = I √(1 - 4t)`. -/
noncomputable def gI (t : ℝ) : ℂ := I * ((Real.sqrt (1 - 4 * t) : ℝ) : ℂ)

lemma im_gI (t : ℝ) : (gI t).im = Real.sqrt (1 - 4 * t) := by simp [gI]

lemma gI_zero : gI 0 = I := by simp [gI]

/-- `g_t(I) = I √(1 - 4t)` solves `ġ = 2 / g` (the Loewner equation for `W = 0`) for `t < 1/4`. -/
theorem hasDerivAt_gI {t : ℝ} (ht : t < 1 / 4) :
    HasDerivAt gI (loewnerField (fun _ => 0) t (gI t)) t := by
  have hpos : 0 < 1 - 4 * t := by linarith
  have hs : 0 < Real.sqrt (1 - 4 * t) := Real.sqrt_pos.mpr hpos
  have h1 : HasDerivAt (fun u : ℝ => 1 - 4 * u) (-4) t := by
    simpa using ((hasDerivAt_id t).const_mul 4).const_sub 1
  have h2 := (h1.sqrt hpos.ne').ofReal_comp.const_mul I
  have hs' : ((Real.sqrt (1 - 4 * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hval : loewnerField (fun _ => 0) t (gI t) =
      I * (((-4) / (2 * Real.sqrt (1 - 4 * t)) : ℝ) : ℂ) := by
    simp only [loewnerField_apply, gI, Complex.ofReal_zero, sub_zero]
    push_cast
    field_simp
    ring_nf
    simp
  rw [hval]
  exact h2

lemma gI_mem_upper {t : ℝ} (ht : t < 1 / 4) : gI t ∈ upperHalfPlaneSet := by
  rw [mem_upperHalfPlane, im_gI]
  exact Real.sqrt_pos.mpr (by linarith)

lemma continuousOn_gI {b : ℝ} (hb : b < 1 / 4) : ContinuousOn gI (Icc 0 b) :=
  fun t ht => (hasDerivAt_gI (by linarith [ht.2])).continuousAt.continuousWithinAt

-- `I` lies in the strip `{Im ≥ 1}`, which lies in `ℍ`.
example : I ∈ loewnerStrip 1 := by simp
example : loewnerStrip 1 ⊆ upperHalfPlaneSet := loewnerStrip_subset_upperHalfPlane one_pos

-- `‖loewnerField 0 t I‖ ≤ 2 / 1`, and the bound is attained.
example (t : ℝ) : ‖loewnerField (fun _ => 0) t I‖ ≤ 2 / 1 :=
  loewnerField_norm_le _ one_pos t (by simp)
example (t : ℝ) : ‖loewnerField (fun _ => 0) t I‖ = 2 := by simp

-- Lipschitz bound on the strip `{Im ≥ 1}` for `W = 0`.
example (t : ℝ) :
    LipschitzOnWith ((2 / 1 ^ 2 : ℝ).toNNReal) (loewnerField (fun _ => 0) t) (loewnerStrip 1) :=
  loewnerField_lipschitzOnWith _ one_pos t

-- Picard–Lindelöf data for `W = 0`, `z₀ = I`, `t₀ = 0`.
example := isPicardLindelof_loewnerField (W := fun _ => 0) continuous_const
  (z₀ := I) (by simp) 0

-- Local existence through `I` at `t₀ = 0`: a solution with `g 0 = I` and a derivative at `0`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = I ∧
    HasDerivWithinAt g (loewnerField (fun _ => 0) 0 I) (Icc (0 - ε) (0 + ε)) 0 := by
  obtain ⟨ε, hε, g, hg0, hgd⟩ :=
    exists_isLoewnerSolutionOn_Icc (W := fun _ => 0) continuous_const (z₀ := I) (by simp) 0
  refine ⟨ε, hε, g, hg0, ?_⟩
  simpa [hg0] using hgd 0 ⟨by linarith, by linarith⟩

-- Two-sided derivative form, driving function `W = id`, start `1 + I` at `t₀ = 1`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 1 = 1 + I ∧
    HasDerivAt g (loewnerField id 1 (1 + I)) 1 := by
  obtain ⟨ε, hε, g, hg0, hgd⟩ :=
    exists_isLoewnerSolution_hasDerivAt (W := id) continuous_id (z₀ := 1 + I) (by simp) 1
  exact ⟨ε, hε, g, hg0, by simpa [hg0] using hgd 1 ⟨by linarith, by linarith⟩⟩

-- `IsLoewnerSolutionOn` form.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ → ℂ, g 0 I = I ∧
    IsLoewnerSolutionOn (fun _ => 0) g I (Icc (0 - ε) (0 + ε)) :=
  exists_isLoewnerSolutionOn continuous_const (by simp) 0

-- Existence and uniqueness: the existence part, with `g 0 = I`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = I := by
  obtain ⟨ε, hε, g, ⟨hg0, -⟩, -⟩ :=
    exists_unique_loewnerSolution (W := fun _ => 0) continuous_const (z₀ := I) (by simp) 0
  exact ⟨ε, hε, g, hg0⟩

-- The explicit solution stays in `{Im ≥ 1/2}` for `t ≤ 3/16`.
lemma gI_mem_strip {t : ℝ} (ht : t ≤ 3 / 16) : gI t ∈ loewnerStrip (1 / 2) := by
  rw [mem_loewnerStrip, im_gI]
  exact Real.le_sqrt_of_sq_le (by linarith)

-- Uniqueness: a solution `h` through `I` staying in `{Im ≥ 1/2}` on `(-1/8, 1/8)` is `I √(1 - 4t)`.
example (h : ℝ → ℂ) (h0 : h 0 = I)
    (hh : ∀ t ∈ Ioo (-1 / 8 : ℝ) (1 / 8),
      HasDerivAt h (loewnerField (fun _ => 0) t (h t)) t ∧ h t ∈ loewnerStrip (1 / 2)) :
    EqOn gI h (Ioo (-1 / 8) (1 / 8)) :=
  loewnerSolution_unique_Ioo (t₀ := 0) (by norm_num) ⟨by norm_num, by norm_num⟩
    (fun t ht => ⟨hasDerivAt_gI (by linarith [ht.2]), gI_mem_strip (by linarith [ht.2])⟩) hh
    (by rw [gI_zero, h0])

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerODE
