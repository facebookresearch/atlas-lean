/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerExistence

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.LoewnerExistence`

* `loewner_local_existence` with the constant driving function `W = 0` and `z = I` (and with
  `W = id`, `z = 1 + I`); its conclusion gives a trajectory staying in `ℍ`.
* `loewner_local_existence_strip_explicit` (`W = 0`, `z = I`, `ε = 1/8`) together with
  `loewner_solution_unique` identifies the solution with `g_t(I) = I √(1 - 4t)`, so
  `g_{1/8}(I) = I √(1/2)`.
* `loewner_local_existsUnique`, `loewner_local_flow_chart`, `loewner_local_existence_strip`.
-/

@[expose] public section

open StatMech.SLE Complex Set
open UpperHalfPlane (upperHalfPlaneSet)

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerExistence

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

-- Local existence for `W = 0`, `z = I`: some `g` with `g 0 = I` and `g ε ∈ ℍ` for an `ε > 0`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = I ∧ 0 < (g ε).im := by
  obtain ⟨ε, hε, g, hg0, -, hgU⟩ :=
    loewner_local_existence (W := fun _ => 0) continuous_const (z := I) (by simp)
  exact ⟨ε, hε, g, hg0, hgU ε ⟨hε.le, le_rfl⟩⟩

-- Local existence for the nonconstant driving function `W = id` from `z = 1 + I`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = 1 + I ∧
    HasDerivWithinAt g (loewnerField id 0 (1 + I)) (Icc 0 ε) 0 := by
  obtain ⟨ε, hε, g, hg0, hgd, -⟩ :=
    loewner_local_existence (W := id) continuous_id (z := 1 + I) (by simp)
  exact ⟨ε, hε, g, hg0, by simpa [hg0] using hgd 0 ⟨le_rfl, hε.le⟩⟩

-- `loewner_solution_unique` with the explicit solution on `[0, ε]`, `ε < 1/4`.
lemma eqOn_gI {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 4) {g : ℝ → ℂ} (hg0 : g 0 = I)
    (hgc : ContinuousOn g (Icc 0 ε))
    (hgd : ∀ t ∈ Ico 0 ε, HasDerivWithinAt g (loewnerField (fun _ => 0) t (g t)) (Ici t) t)
    (hgu : ∀ t ∈ Icc 0 ε, 0 < (g t).im) : EqOn g gI (Icc 0 ε) :=
  loewner_solution_unique hε hg0 gI_zero hgc hgd hgu (continuousOn_gI hε')
    (fun t ht => (hasDerivAt_gI (by linarith [ht.2])).hasDerivWithinAt)
    (fun t ht => gI_mem_upper (by linarith [ht.2]))

-- The strip solution of `loewner_local_existence_strip_explicit` for `W = 0`, `z = I` lives on
-- `[0, 1/8]` and equals `I √(1 - 4t)` there, so its value at `1/8` is `I √(1/2)`.
example : ∃ g : ℝ → ℂ, g 0 = I ∧ g (1 / 8) = I * ((Real.sqrt (1 / 2) : ℝ) : ℂ) := by
  obtain ⟨g, hg0, hgd, hgs⟩ :=
    loewner_local_existence_strip_explicit (W := fun _ => 0) continuous_const (z := I) (by simp)
  have hE : I.im ^ 2 / 8 = 1 / 8 := by simp
  rw [hE] at hgd hgs
  refine ⟨g, hg0, ?_⟩
  have heq := eqOn_gI (by norm_num) (by norm_num) hg0
    (fun t ht => (hgd t ht).continuousWithinAt)
    (fun t ht => (hgd t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => lt_of_lt_of_le (by norm_num) (mem_loewnerStrip.mp (hgs t ht)))
    (show (1 / 8 : ℝ) ∈ Icc 0 (1 / 8) by norm_num)
  rw [heq, gI]
  norm_num

-- `loewner_local_existence_strip`: the solution stays in `{Im ≥ 1/2}`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g 0 = I ∧ ∀ t ∈ Icc 0 ε, 1 / 2 ≤ (g t).im := by
  obtain ⟨ε, hε, g, hg0, -, hgs⟩ :=
    loewner_local_existence_strip (W := fun _ => 0) continuous_const (z := I) (by simp)
  exact ⟨ε, hε, g, hg0, fun t ht => by simpa using hgs t ht⟩

-- `loewner_local_existsUnique`: the unique solution through `I` agrees with `I √(1 - 4t)` on
-- `[0, min ε (1/8)]`.
example : ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, EqOn g gI (Icc 0 (min ε (1 / 8))) := by
  obtain ⟨ε, hε, g, ⟨hg0, hgd, hgU⟩, -⟩ :=
    loewner_local_existsUnique (W := fun _ => 0) continuous_const (z := I) (by simp)
  set m := min ε (1 / 8) with hm
  have hm0 : 0 < m := lt_min hε (by norm_num)
  have hmε : m ≤ ε := min_le_left _ _
  have hsub : Icc 0 m ⊆ Icc 0 ε := Icc_subset_Icc_right hmε
  refine ⟨ε, hε, g, eqOn_gI hm0 (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) hg0
    (fun t ht => ((hgd t (hsub ht)).mono hsub).continuousWithinAt) (fun t ht => ?_)
    (fun t ht => hgU t (hsub ht))⟩
  exact (hgd t (hsub (Ico_subset_Icc_self ht))).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem ⟨ht.1, lt_of_lt_of_le ht.2 hmε⟩)

-- `loewner_local_flow_chart` for `W = 0` around `z₀ = I`, `t₀ = 0`: `α I 0 = I`.
example : ∃ α : ℂ → ℝ → ℂ, α I 0 = I := by
  obtain ⟨α, hα, -⟩ :=
    loewner_local_flow_chart (W := fun _ => 0) continuous_const (z₀ := I) (by simp) 0
  exact ⟨α, (hα I (Metric.mem_closedBall_self (by simp))).1⟩

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerExistence
