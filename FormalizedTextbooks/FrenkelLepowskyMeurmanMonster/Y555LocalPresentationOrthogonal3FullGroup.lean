/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The independent full isometry group of the explicit nonsingular finite Cartan form. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3Form
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationOrthogonal3NormCoordinates
public import Mathlib.GroupTheory.Commutator.Basic

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix

/-- All invertible matrices preserving the actual finite Cartan form. -/
def y322Orthogonal3FullGroup : Subgroup (Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) where
  carrier := {g | g.val.transpose * y322Orthogonal3Gram * g.val = y322Orthogonal3Gram}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change (g * h).val.transpose * y322Orthogonal3Gram * (g * h).val = y322Orthogonal3Gram
    change g.val.transpose * y322Orthogonal3Gram * g.val = y322Orthogonal3Gram at hg
    change h.val.transpose * y322Orthogonal3Gram * h.val = y322Orthogonal3Gram at hh
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc
      _ = h.val.transpose * (g.val.transpose * y322Orthogonal3Gram * g.val) * h.val := by
        simp only [mul_assoc]
      _ = y322Orthogonal3Gram := by rw [hg, hh]
  inv_mem' {g} hg := by
    change (g⁻¹).val.transpose * y322Orthogonal3Gram * (g⁻¹).val = y322Orthogonal3Gram
    change g.val.transpose * y322Orthogonal3Gram * g.val = y322Orthogonal3Gram at hg
    have hm : g.val * (g⁻¹).val = 1 := g.val_inv
    calc
      _ = (g⁻¹).val.transpose * (g.val.transpose * y322Orthogonal3Gram * g.val) *
          (g⁻¹).val := by rw [hg]
      _ = (g.val * (g⁻¹).val).transpose * y322Orthogonal3Gram *
          (g.val * (g⁻¹).val) := by
        rw [Matrix.transpose_mul]
        simp only [mul_assoc]
      _ = y322Orthogonal3Gram := by rw [hm]; simp

/-- The independently defined full finite-form isometry group is finite. -/
theorem y322Orthogonal3FullGroup_finite : Finite y322Orthogonal3FullGroup := by
  infer_instance

/-- Every original source reflection image lies in the independently defined full isometry group. -/
theorem y322Orthogonal3Image_le_full : y322Orthogonal3Image ≤ y322Orthogonal3FullGroup := by
  intro g hg
  exact y322Orthogonal3Image_preserves g hg

/-- Every independent form isometry preserves the exact quadratic value of actual vectors. -/
theorem y322Orthogonal3FullGroup_norm
    (g : Matrix.GeneralLinearGroup (Fin 7) (ZMod 3)) (hg : g ∈ y322Orthogonal3FullGroup)
    (v : Fin 7 → ZMod 3) :
    y322Orthogonal3VectorNorm (g.val *ᵥ v) = y322Orthogonal3VectorNorm v := by
  unfold y322Orthogonal3VectorNorm
  rw [dotProduct_comm (g.val *ᵥ v)]
  rw [← Matrix.dotProduct_transpose_mulVec]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

/-- The derived subgroup of the independently defined full finite isometry group. -/
def y322Orthogonal3FullDerived : Subgroup y322Orthogonal3FullGroup :=
  commutator y322Orthogonal3FullGroup

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
