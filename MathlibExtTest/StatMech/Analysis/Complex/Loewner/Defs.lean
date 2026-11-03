/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.Loewner.Defs
public import Mathlib

/-!
# Tests for `MathlibExt.Analysis.Complex.Loewner.Defs`

* `loewnerField` is computed at simple inputs: for the constant driving function `W = 0` it is
  `w ↦ 2 / w`, so `loewnerField 0 t I = -2 I` and `loewnerField 0 t 1 = 2`.
* `IsLoewnerSolutionAt` and `IsLoewnerSolutionOn` hold for the explicit solution
  `g_t(I) = I √(1 - 4t)` of the Loewner equation with `W = 0` (the restriction to `z = I` of
  `g_t(z) = √(z² + 4t)`), for `t < 1/4` and on `[0, 1/8]`.
* Membership in `upperHalfPlaneSet`, `closedUpperHalfPlane`, `realLine`; `IsCompactHull ∅`;
  `HasHalfPlaneCapacity id 0` and uniqueness of the capacity; `sleDriving` at `κ = 0` and `κ = 4`.
-/

@[expose] public section

open StatMech.SLE Complex
open UpperHalfPlane (upperHalfPlaneSet)

namespace MathlibExtTest.StatMech.Analysis.Complex.Loewner.Defs

/-- The explicit Loewner trajectory of `z = I` for `W = 0`: `g_t(I) = I √(1 - 4t)`. -/
noncomputable def gI (t : ℝ) : ℂ := I * ((Real.sqrt (1 - 4 * t) : ℝ) : ℂ)

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
    simp [Complex.I_sq]
  rw [hval]
  exact h2

-- `loewnerField` for `W = 0` at `w = I` is `2 / I = -2 I`.
example (t : ℝ) : loewnerField (fun _ => 0) t I = -2 * I := by
  simp [div_eq_mul_inv, Complex.inv_I]

-- `loewnerField` for `W = 0` at `w = 1` is `2`.
example (t : ℝ) : loewnerField (fun _ => 0) t 1 = 2 := by simp

-- `loewnerField W t (W t + 2) = 1` for any driving function.
example (W : ℝ → ℝ) (t : ℝ) : loewnerField W t ((W t : ℂ) + 2) = 1 := by simp

-- With Lean's `x / 0 = 0`, the field vanishes at the driving point.
example (W : ℝ → ℝ) (t : ℝ) : loewnerField W t (W t) = 0 := by simp

-- `I ∈ ℍ`, `0` is in the closed half-plane and on the real line, `-I ∉ closedUpperHalfPlane`.
example : I ∈ upperHalfPlaneSet := by simp
example : (0 : ℂ) ∈ closedUpperHalfPlane ∧ (0 : ℂ) ∈ realLine := by simp
example : -I ∉ closedUpperHalfPlane := by simp
example : (3 : ℂ) ∉ upperHalfPlaneSet := by simp

-- `gI 0 = I`.
example : gI 0 = I := by simp [gI]

-- `IsLoewnerSolutionAt` holds for `g_t(z) = gI t` at `z = I`, every `t < 1/4`.
example {t : ℝ} (ht : t < 1 / 4) :
    IsLoewnerSolutionAt (fun _ => 0) (fun s _ => gI s) I t :=
  hasDerivAt_gI ht

-- `IsLoewnerSolutionOn` holds for the same family on `[0, 1/8]`.
example : IsLoewnerSolutionOn (fun _ => 0) (fun s _ => gI s) I (Set.Icc 0 (1 / 8)) :=
  fun t ht => (hasDerivAt_gI (by linarith [ht.2])).hasDerivWithinAt

-- The empty set is a compact `ℍ`-hull (a nonempty one is in the `LoewnerMaximal` tests).
example : IsCompactHull (∅ : Set ℂ) := isCompactHull_empty
example : IsSimplyConnected (upperHalfPlaneSet \ (∅ : Set ℂ)) :=
  isCompactHull_empty.complement_simplyConnected
example : IsConnected (upperHalfPlaneSet \ (∅ : Set ℂ)) :=
  isCompactHull_empty.complement_connected

-- `HasHalfPlaneCapacity id 0`, and capacities are unique.
example : HasHalfPlaneCapacity id 0 := hasHalfPlaneCapacity_id
example (a : ℝ) (h : HasHalfPlaneCapacity id a) : a = 0 :=
  h.unique hasHalfPlaneCapacity_id

-- `sleDriving 0 B ω = 0` and `sleDriving 4 B ω t = 2 B_t(ω)`.
example (B : ℝ → Unit → ℝ) (t : ℝ) : sleDriving 0 B () t = 0 := sleDriving_kappa_zero B () t
example (B : ℝ → Unit → ℝ) (t : ℝ) : sleDriving 4 B () t = 2 * B t () := by
  have : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [this]

-- An ordinary `IsChordalSLE` client receives continuous drivers from the strengthened predicate.
example {Ω : Type*} [MeasurableSpace Ω] (κ : ℝ) (B : ℝ → Ω → ℝ)
    (P : MeasureTheory.Measure Ω)
    (D : Ω → ℝ → Set ℂ) (g : Ω → ℝ → ℂ → ℂ) (h : IsChordalSLE κ B P D g) :
    ∀ᵐ ω ∂P, Continuous (sleDriving κ B ω) := by
  filter_upwards [h.loewner] with ω hω
  exact hω.continuous_driving

end MathlibExtTest.StatMech.Analysis.Complex.Loewner.Defs
