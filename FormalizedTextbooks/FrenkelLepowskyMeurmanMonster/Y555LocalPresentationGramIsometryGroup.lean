/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Independent matrix isometry groups and exact coordinate changes for finite forms. -/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The independent group of all invertible coordinate matrices preserving a given Gram matrix. -/
def y322GramIsometryGroup {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (gram : Matrix ι ι R) : Subgroup (Matrix.GeneralLinearGroup ι R) where
  carrier := {g | g.val.transpose * gram * g.val = gram}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change (g * h).val.transpose * gram * (g * h).val = gram
    change g.val.transpose * gram * g.val = gram at hg
    change h.val.transpose * gram * h.val = gram at hh
    simp only [Units.val_mul, Matrix.transpose_mul]
    calc
      _ = h.val.transpose * (g.val.transpose * gram * g.val) * h.val := by
        simp only [mul_assoc]
      _ = gram := by rw [hg, hh]
  inv_mem' {g} hg := by
    change (g⁻¹).val.transpose * gram * (g⁻¹).val = gram
    change g.val.transpose * gram * g.val = gram at hg
    have hm : g.val * (g⁻¹).val = 1 := g.val_inv
    calc
      _ = (g⁻¹).val.transpose * (g.val.transpose * gram * g.val) * (g⁻¹).val := by rw [hg]
      _ = (g.val * (g⁻¹).val).transpose * gram * (g.val * (g⁻¹).val) := by
        rw [Matrix.transpose_mul]
        simp only [mul_assoc]
      _ = gram := by rw [hm]; simp

/-- An exact invertible basis change transports every independent Gram isometry. -/
theorem y322GramIsometryGroup_conjugate {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [CommRing R] (gram : Matrix ι ι R)
    (basis g : Matrix.GeneralLinearGroup ι R) (hg : g ∈ y322GramIsometryGroup gram) :
    basis⁻¹ * g * basis ∈ y322GramIsometryGroup (basis.val.transpose * gram * basis.val) := by
  change g.val.transpose * gram * g.val = gram at hg
  have hb : basis.val * (basis⁻¹).val = 1 := basis.val_inv
  have ht : (basis⁻¹).val.transpose * basis.val.transpose = 1 := by
    rw [← Matrix.transpose_mul, hb, Matrix.transpose_one]
  change (basis⁻¹ * g * basis).val.transpose * (basis.val.transpose * gram * basis.val) *
    (basis⁻¹ * g * basis).val = basis.val.transpose * gram * basis.val
  simp only [Units.val_mul, Matrix.transpose_mul]
  calc
    _ = basis.val.transpose * g.val.transpose *
        ((basis⁻¹).val.transpose * basis.val.transpose) * gram *
        (basis.val * (basis⁻¹).val) * g.val * basis.val := by simp only [mul_assoc]
    _ = basis.val.transpose * (g.val.transpose * gram * g.val) * basis.val := by
      rw [ht, hb]
      simp only [mul_one, mul_assoc]
    _ = basis.val.transpose * gram * basis.val := by rw [hg]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
