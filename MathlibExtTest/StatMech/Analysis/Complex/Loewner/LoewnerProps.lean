/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.LoewnerProps

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.LoewnerProps`

* `im_loewnerField`, `re_loewnerField`, `loewnerReflection` at simple inputs.
* `antitoneOn_im_of_isLoewnerSolution` and `mem_upperHalfPlane_of_isLoewnerSolution` for the
  explicit solution `g_t(I) = I √(1 - 4t)` of the Loewner equation with `W = 0`, on `[0, 1/8]`,
  `δ = 1/2`.
* `HasHalfPlaneCapacity`: `z ↦ z + 1/z` has capacity `1`; by `hasHalfPlaneCapacity_comp` and
  `hcap_linear_of_decomposition` its self-composition has capacity `2`.
* `HasCapacityRate` for the constant family `id`; `MonotoneHullFamily` for the constant family `∅`.
-/

@[expose] public section

open StatMech.SLE Complex Set
open UpperHalfPlane (upperHalfPlaneSet)

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerProps

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

-- `Im (2 / I) = -2` via `im_loewnerField`, and `Re (2 / 1) = 2` via `re_loewnerField`.
example (t : ℝ) : (loewnerField (fun _ => 0) t I).im = -2 := by
  rw [im_loewnerField]; simp
example (t : ℝ) : (loewnerField (fun _ => 0) t 1).re = 2 := by
  rw [re_loewnerField]; simp

-- The reflection `z ↦ -z̄` fixes `I` and sends `1` to `-1`.
example : loewnerReflection I = I := by simp [loewnerReflection]
example : loewnerReflection 1 = -1 := by simp [loewnerReflection]

-- Reflecting the field: the image for `W` is the field for `-W` at the reflected point.
example (t : ℝ) : loewnerReflection (loewnerField id t I) =
    loewnerField (fun s => -id s) t (loewnerReflection I) :=
  loewnerReflection_loewnerField id t I

lemma gI_mem_strip {t : ℝ} (ht : t ≤ 3 / 16) : gI t ∈ loewnerStrip (1 / 2) := by
  rw [mem_loewnerStrip, im_gI]
  exact Real.le_sqrt_of_sq_le (by linarith)

-- `Im g_t(I)` is antitone on `[0, 1/8]`.
example : AntitoneOn (fun s => (gI s).im) (Icc 0 (1 / 8)) :=
  antitoneOn_im_of_isLoewnerSolution (W := fun _ => 0) (δ := 1 / 2) (by norm_num)
    (Complex.continuous_im.comp_continuousOn (continuousOn_gI (by norm_num)))
    (fun t ht => hasDerivAt_gI (by linarith [ht.2]))
    (fun t ht => gI_mem_strip (by linarith [ht.2]))

-- The trajectory stays in `ℍ` on `[0, 1/8]`; in particular `g_{1/8}(I) ∈ ℍ`.
example : gI (1 / 8) ∈ upperHalfPlaneSet :=
  mem_upperHalfPlane_of_isLoewnerSolution (W := fun _ => 0) (δ := 1 / 2) (a := 0) (b := 1 / 8)
    (by norm_num) (Complex.continuous_im.comp_continuousOn (continuousOn_gI (by norm_num)))
    (fun t ht => (hasDerivAt_gI (by linarith [ht.2])).hasDerivWithinAt)
    (fun t ht => gI_mem_strip (by linarith [ht.2])) (by simp [gI_zero]) _
    ⟨by norm_num, le_rfl⟩

/-- `z ↦ z + 1/z` has half-plane capacity `1`. -/
lemma hasHalfPlaneCapacity_add_inv : HasHalfPlaneCapacity (fun z : ℂ => z + z⁻¹) 1 := by
  refine ⟨?_, ?_⟩
  · simp only [add_sub_cancel_left]
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  · simp only [add_sub_cancel_left, Complex.ofReal_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_zero_cocompact] with z hz
    exact (mul_inv_cancel₀ hz).symm

-- Capacity is additive: the self-composition of `z + 1/z` has capacity `1 + 1`.
example : HasHalfPlaneCapacity ((fun z : ℂ => z + z⁻¹) ∘ (fun z : ℂ => z + z⁻¹)) (1 + 1) :=
  hasHalfPlaneCapacity_comp hasHalfPlaneCapacity_add_inv hasHalfPlaneCapacity_add_inv

-- The same via `hcap_linear_of_decomposition` with `cs = 1`, `ct = 2`.
example : HasHalfPlaneCapacity ((fun z : ℂ => z + z⁻¹) ∘ (fun z : ℂ => z + z⁻¹)) 2 :=
  hcap_linear_of_decomposition rfl hasHalfPlaneCapacity_add_inv
    (by norm_num; exact hasHalfPlaneCapacity_add_inv)

-- `HasCapacityRate` for the constant family `id` with rate `0`, and its time-zero consequence.
example : HasCapacityRate (fun _ => id) 0 := fun t _ => by
  simpa using hasHalfPlaneCapacity_id
example : HasHalfPlaneCapacity id 0 :=
  HasCapacityRate.hcap_zero (g := fun _ => id) (a := 0)
    (fun t _ => by simpa using hasHalfPlaneCapacity_id)

-- The constant family `∅` is a monotone family of compact hulls.
example : MonotoneHullFamily (fun _ : ℝ => (∅ : Set ℂ)) :=
  ⟨fun _ => isCompactHull_empty, fun _ _ _ => le_rfl⟩

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.LoewnerProps
