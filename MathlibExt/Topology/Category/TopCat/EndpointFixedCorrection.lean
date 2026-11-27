/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Topology.Homotopy.TopCat.Basic
import Mathlib.Topology.Order.ProjIcc

/-!
# Endpoint-fixed corrections of homotopies

This file packages a corrected homotopy together with a comparison from the
raw homotopy that is fixed at both original homotopy endpoints. It also gives
the reparametrizations used when correcting a successor homotopy.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace TopCat

/-- The two time-endpoint faces in the domain of a homotopy. -/
def homotopyEndpointFaces (X : TopCat.{u}) : Set (unitInterval × X) :=
  {p | p.1 = 0 ∨ p.1 = 1}

@[simp]
theorem mem_homotopyEndpointFaces_iff (X : TopCat.{u})
    (p : unitInterval × X) :
    p ∈ homotopyEndpointFaces X ↔ p.1 = 0 ∨ p.1 = 1 :=
  Iff.rfl

/-- A corrected homotopy with an endpoint-fixed comparison from the raw
homotopy. -/
structure EndpointFixedCorrection
    {X Y : TopCat.{u}} {f₀ f₁ : X ⟶ Y} (raw : Homotopy f₀ f₁) where
  /-- The corrected homotopy, with the same endpoint maps. -/
  corrected : Homotopy f₀ f₁
  /-- A homotopy from the raw to the corrected parametrized map, fixed when
  the original homotopy time is zero or one. -/
  comparison :
    ContinuousMap.HomotopyRel raw.toContinuousMap corrected.toContinuousMap
      (homotopyEndpointFaces X)

namespace EndpointFixedCorrection

variable {X Y : TopCat.{u}} {f₀ f₁ : X ⟶ Y}

/-- The reflexive endpoint-fixed correction. -/
def refl (raw : Homotopy f₀ f₁) : EndpointFixedCorrection raw where
  corrected := raw
  comparison := ContinuousMap.HomotopyRel.refl raw.toContinuousMap
    (homotopyEndpointFaces X)

/-- Two endpoint-fixed corrections with the same corrected homotopy and
comparison values are equal. -/
@[ext]
theorem ext {raw : Homotopy f₀ f₁} {c c' : EndpointFixedCorrection raw}
    (h_corrected : ∀ p, c.corrected p = c'.corrected p)
    (h_comparison : ∀ q, c.comparison q = c'.comparison q) :
    c = c' := by
  obtain ⟨K₁, H₁⟩ := c
  obtain ⟨K₂, H₂⟩ := c'
  have hK : K₁ = K₂ := ContinuousMap.Homotopy.ext h_corrected
  subst hK
  have hH : H₁ = H₂ := ContinuousMap.HomotopyWith.ext h_comparison
  subst hH
  rfl

@[simp]
theorem comparison_zero {raw : Homotopy f₀ f₁}
    (c : EndpointFixedCorrection raw) (p : unitInterval × X) :
    c.comparison (0, p) = raw p :=
  c.comparison.apply_zero p

@[simp]
theorem comparison_one {raw : Homotopy f₀ f₁}
    (c : EndpointFixedCorrection raw) (p : unitInterval × X) :
    c.comparison (1, p) = c.corrected p :=
  c.comparison.apply_one p

theorem comparison_original_zero {raw : Homotopy f₀ f₁}
    (c : EndpointFixedCorrection raw) (s : unitInterval) (x : X) :
    c.comparison (s, (0, x)) = raw (0, x) :=
  c.comparison.eq_fst s (Or.inl rfl)

theorem comparison_original_one {raw : Homotopy f₀ f₁}
    (c : EndpointFixedCorrection raw) (s : unitInterval) (x : X) :
    c.comparison (s, (1, x)) = raw (1, x) :=
  c.comparison.eq_fst s (Or.inr rfl)

end EndpointFixedCorrection

/-- The tail reparametrization used by `Homotopy.refl.trans`: it is zero on
the first half and `2t-1` on the second half. -/
def homotopyReflTransReparam : C(unitInterval, unitInterval) where
  toFun t := Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1)
  continuous_toFun := continuous_projIcc.comp
    ((continuous_const.mul continuous_subtype_val).sub continuous_const)

@[simp]
theorem homotopyReflTransReparam_zero :
    homotopyReflTransReparam 0 = 0 := by
  apply Subtype.ext
  simp [homotopyReflTransReparam]

@[simp]
theorem homotopyReflTransReparam_one :
    homotopyReflTransReparam 1 = 1 := by
  apply Subtype.ext
  simp [homotopyReflTransReparam]
  norm_num

theorem homotopyReflTransReparam_eq_zero_of_le
    (t : unitInterval) (ht : (t : ℝ) ≤ 1 / 2) :
    homotopyReflTransReparam t = 0 := by
  change Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = 0
  apply projIcc_eq_zero.mpr
  nlinarith

theorem homotopyReflTransReparam_eq_of_not_le
    (t : unitInterval) (ht : ¬ (t : ℝ) ≤ 1 / 2) :
    homotopyReflTransReparam t =
      ⟨2 * (t : ℝ) - 1, by
        constructor
        · nlinarith
        · nlinarith [t.2.2]⟩ := by
  change Set.projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1) = _
  apply Set.projIcc_of_mem

/-- Linear interpolation from the tail reparametrization to the identity. -/
def homotopyReflTransBlend : C(unitInterval × unitInterval, unitInterval) where
  toFun p := Set.Icc.convexComb (homotopyReflTransReparam p.2) p.2 p.1
  continuous_toFun := Set.Icc.continuous_convexComb_prod.comp
    ((homotopyReflTransReparam.continuous.comp continuous_snd).prodMk
      (continuous_snd.prodMk continuous_fst))

@[simp]
theorem homotopyReflTransBlend_zero (t : unitInterval) :
    homotopyReflTransBlend (0, t) = homotopyReflTransReparam t :=
  Set.Icc.convexComb_zero _ _

@[simp]
theorem homotopyReflTransBlend_one (t : unitInterval) :
    homotopyReflTransBlend (1, t) = t :=
  Set.Icc.convexComb_one _ _

@[simp]
theorem homotopyReflTransBlend_left (s : unitInterval) :
    homotopyReflTransBlend (s, 0) = 0 := by
  change Set.Icc.convexComb (homotopyReflTransReparam 0) 0 s = 0
  rw [homotopyReflTransReparam_zero, Set.Icc.convexComb_eq]

@[simp]
theorem homotopyReflTransBlend_right (s : unitInterval) :
    homotopyReflTransBlend (s, 1) = 1 := by
  change Set.Icc.convexComb (homotopyReflTransReparam 1) 1 s = 1
  rw [homotopyReflTransReparam_one, Set.Icc.convexComb_eq]

/-- Concatenating a constant homotopy before `K` is exactly precomposition by
the tail reparametrization. -/
theorem homotopy_refl_trans_apply
    {X Y : TopCat.{u}} {f₀ f₁ : X ⟶ Y} (K : Homotopy f₀ f₁)
    (t : unitInterval) (x : X) :
    ((Homotopy.refl f₀).trans K) (t, x) =
      K (homotopyReflTransReparam t, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split_ifs with ht
  · rw [homotopyReflTransReparam_eq_zero_of_le t ht, K.apply_zero]
    rfl
  · rw [homotopyReflTransReparam_eq_of_not_le t ht]

end TopCat

end
