/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.MatrixSpace.Blowup
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Range and rank of tensoring a matrix with an identity

Let i be any row type, j a finite column type, d a finite identity index and A:Matrix i j R.
The Kronecker matrix A⊗I_d acts independently on the d columns. Over a commutative semiring,
its range consists of vectors whose every d-column lies in range(A). Over a field,
rank(A⊗I_d)=rank(A)|d|. Empty identity indices are included.
-/

@[expose] public section

universe u v w z

namespace Matrix

open scoped Kronecker

variable {i : Type v} {j : Type w} {d : Type z}
variable [Fintype j] [Fintype d] [DecidableEq d]

section CommSemiring

variable {R : Type u} [CommSemiring R]

private theorem kronecker_one_project (A : Matrix i j R) (x : j × d → R) (a : d) :
    (fun k : i => ((A ⊗ₖ (1 : Matrix d d R)) *ᵥ x) (k, a)) =
      A *ᵥ (fun k : j => x (k, a)) := by
  ext k
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

private theorem kronecker_one_insert (A : Matrix i j R) (a : d) (x : j → R) :
    (A ⊗ₖ (1 : Matrix d d R)) *ᵥ LinearMap.columnInsert a x =
      LinearMap.columnInsert a (A *ᵥ x) := by
  ext ⟨k, b⟩
  have hc := congrFun (kronecker_one_project A (LinearMap.columnInsert a x) b) k
  by_cases h : b = a
  · subst b
    simpa [LinearMap.columnInsert_apply] using hc
  · have hp : (fun l : j => LinearMap.columnInsert a x (l, b)) = 0 := by
      ext l
      simp [LinearMap.columnInsert_apply, h]
    rw [hp, Matrix.mulVec_zero] at hc
    simpa [LinearMap.columnInsert_apply, h] using hc

/-- **Column amplification of the range under a Kronecker identity.**

Let R be a commutative semiring, i any row type, j,d finite index types and A:Matrix i j R.
Then range((A⊗I_d).mulVecLin)=range(A.mulVecLin).columnAmplification d, the vectors with each
d-column in range(A).
-/
theorem range_kronecker_one (A : Matrix i j R) :
    (A ⊗ₖ (1 : Matrix d d R)).mulVecLin.range = A.mulVecLin.range.columnAmplification d := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply Submodule.mem_columnAmplification.mpr
    intro a
    exact ⟨fun k : j => x (k, a), (kronecker_one_project A x a).symm⟩
  · rw [Submodule.columnAmplification_eq_iSup]
    refine iSup_le fun a => ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx⟩ := hy
    refine ⟨LinearMap.columnInsert a x, ?_⟩
    change (A ⊗ₖ (1 : Matrix d d R)) *ᵥ LinearMap.columnInsert a x = LinearMap.columnInsert a y
    rw [kronecker_one_insert]
    exact congrArg (LinearMap.columnInsert a) hx

end CommSemiring

section Field

variable {K : Type u} [Field K]

/-- **Rank multiplied by the size of a Kronecker identity.**

Let K be a field, i any row type, j,d finite index types and A:Matrix i j K. Then
rank(A⊗I_d)=rank(A)*|d|, also when d is empty.
-/
theorem rank_kronecker_one (A : Matrix i j K) :
    (A ⊗ₖ (1 : Matrix d d K)).rank = A.rank * Fintype.card d := by
  change Module.finrank K (A ⊗ₖ (1 : Matrix d d K)).mulVecLin.range =
    Module.finrank K A.mulVecLin.range * Fintype.card d
  rw [range_kronecker_one, Submodule.finrank_columnAmplification]

end Field

end Matrix
