/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.CokernelLengthComposition
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Full matrix cokernels under row and column reindexing

Independent row and column equivalences act through the existing actual
linear maps on the source and target. Their full cokernel lengths agree,
and the existing determinant sign is a unit, preserving its order.
-/

@[expose] public section
noncomputable section

universe u v w v' w'

namespace Matrix

variable {R : Type u} [CommRing R]

/-- Independent row and column reindexing preserves the full cokernel
length of the actual matrix map, including rectangular and empty matrices. -/
theorem length_coker_reindex {m : Type v} {n : Type w} {m' : Type v'} {n' : Type w'}
    [Fintype n] [Fintype n'] (er : m ≃ m') (ec : n ≃ n') (A : Matrix m n R) :
    Module.length R ((m' → R) ⧸ (A.reindex er ec).mulVecLin.range) =
      Module.length R ((m → R) ⧸ A.mulVecLin.range) := by
  rw [mulVecLin_reindex]
  exact (LinearMap.length_coker_precompose_equiv
    ((LinearEquiv.funCongrLeft R R er.symm).toLinearMap.comp A.mulVecLin)
    (LinearEquiv.funCongrLeft R R ec)).trans
      (LinearMap.length_coker_postcompose_equiv A.mulVecLin (LinearEquiv.funCongrLeft R R er.symm))

/-- The actual sign from independent row and column reindexing is a unit,
so the order of the determinant is unchanged over any commutative ring. -/
theorem ord_det_reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (er ec : ι ≃ κ) (A : Matrix ι ι R) :
    Ring.ord R (A.reindex er ec).det = Ring.ord R A.det := by
  rw [det_reindex]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ec.trans er.symm)) with h | h <;> simp [h]

/-- Independent row and column reindexing preserves nonvanishing of the
original determinant, through the actual unit sign. -/
theorem det_reindex_ne_zero_iff {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (er ec : ι ≃ κ) (A : Matrix ι ι R) :
    (A.reindex er ec).det ≠ 0 ↔ A.det ≠ 0 := by
  rw [det_reindex]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ec.trans er.symm)) with h | h <;> simp [h]

end Matrix
