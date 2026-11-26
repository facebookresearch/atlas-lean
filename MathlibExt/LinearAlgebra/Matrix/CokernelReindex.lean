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
# Matrix cokernels under independent row and column reindexing

Let R be a commutative ring and A an m×n matrix with finite column type n and arbitrary row
type m. Equivalences er:m≃m′ and ec:n≃n′ preserve the module length of the full cokernel. For
square finite matrices they preserve determinant nonvanishing and ord_R(det A), where
ord_R(a)=length_R(R/(a)).
-/

@[expose] public section
noncomputable section

universe u v w v' w'

namespace Matrix

variable {R : Type u} [CommRing R]

/-- **Cokernel length is invariant under row and column reindexing.**

Let R be a commutative ring, n,n′ finite column types, m,m′ arbitrary row types, er:m≃m′,
ec:n≃n′ and A:Matrix m n R. Then length_R(R^m′/range((A.reindex er
ec).mulVecLin))=length_R(R^m/range(A.mulVecLin)).
-/
theorem length_coker_reindex {m : Type v} {n : Type w} {m' : Type v'} {n' : Type w'}
    [Fintype n] [Fintype n'] (er : m ≃ m') (ec : n ≃ n') (A : Matrix m n R) :
    Module.length R ((m' → R) ⧸ (A.reindex er ec).mulVecLin.range) =
      Module.length R ((m → R) ⧸ A.mulVecLin.range) := by
  rw [mulVecLin_reindex]
  exact (LinearMap.length_coker_precompose_equiv
    ((LinearEquiv.funCongrLeft R R er.symm).toLinearMap.comp A.mulVecLin)
    (LinearEquiv.funCongrLeft R R ec)).trans
      (LinearMap.length_coker_postcompose_equiv A.mulVecLin (LinearEquiv.funCongrLeft R R er.symm))

/-- **Determinant order is invariant under independent reindexing.**

Let R be a commutative ring, I,J finite index types, er,ec:I≃J and A:I×I→R. With
ord_R(a)=length_R(R/(a)), ord_R(det(A.reindex er ec))=ord_R(det A); the determinant changes by
a sign unit.
-/
theorem ord_det_reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (er ec : ι ≃ κ) (A : Matrix ι ι R) :
    Ring.ord R (A.reindex er ec).det = Ring.ord R A.det := by
  rw [det_reindex]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ec.trans er.symm)) with h | h <;> simp [h]

/-- **Reindexing preserves determinant nonvanishing.**

Let R be a commutative ring, I,J finite index types, er,ec:I≃J and A:I×I→R. Then det(A.reindex
er ec)≠0 if and only if det A≠0.
-/
theorem det_reindex_ne_zero_iff {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (er ec : ι ≃ κ) (A : Matrix ι ι R) :
    (A.reindex er ec).det ≠ 0 ↔ A.det ≠ 0 := by
  rw [det_reindex]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (ec.trans er.symm)) with h | h <;> simp [h]

end Matrix
