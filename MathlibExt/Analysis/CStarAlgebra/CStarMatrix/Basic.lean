/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
Norm-bound source: Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean.
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
The adapted norm-bound proof is licensed under Apache 2.0 (Mathlib LICENSE).
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Algebra.Group.Idempotent

import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Basic algebra transport, norms and instances for C-star matrix algebras

Mathlib registers the rectangular scalar-action laws
`CStarMatrix.instIsScalarTower` and `CStarMatrix.instSMulCommClass`, in which
scalars act entrywise through the coefficient action.  This file adds the
square self-action cases, in which the middle action is matrix
multiplication itself.  They are the `CStarMatrix` analogues of
`Matrix.Semiring.isScalarTower` and `Matrix.Semiring.smulCommClass`, and are
required, for example, by `Unitization.instSemiring` over a matrix algebra.

The rectangular multiplication transport and square ring equivalence below
also identify the matrix type copy algebraically without a coefficient unit.

The rectangular operator-norm bound uses the original coefficient norm and
order dictionaries. Its proof extracts the intermediate sum-of-entry-norms
estimate from Mathlib's private `antilipschitzWith_toMatrixAux` proof in
`Mathlib/Analysis/CStarAlgebra/CStarMatrix.lean`, by Frédéric Dupuis.
-/

@[expose] public section

namespace CStarMatrix

universe uA uL uM uN

/-- Let `A` carry multiplication and an additive commutative monoid structure. Let `l`, `m`, `n` be
index types with `m` finite. For `X : Matrix l m A` and `Y : Matrix m n A`, transporting the two
matrices by `ofMatrix` preserves their rectangular product.
-/
@[simp]
theorem of_mul_of {A : Type uA} {l : Type uL} {m : Type uM} {n : Type uN}
    [Mul A] [AddCommMonoid A] [Fintype m]
    (X : Matrix l m A) (Y : Matrix m n A) :
    ofMatrix X * ofMatrix Y = ofMatrix (X * Y) := by
  apply CStarMatrix.ext
  intro i k
  simp only [CStarMatrix.mul_apply, CStarMatrix.ofMatrix_apply, Matrix.mul_apply]

/-- Let `A` be an additive commutative monoid. Let `n` be a finite index type. `A` has a multiplication.
The `CStarMatrix` representation as a ring equivalence, without a coefficient unit.
-/
def ofMatrixNonUnitalRingEquiv {A : Type uA} {n : Type uN}
    [Mul A] [AddCommMonoid A] [Fintype n] :
    Matrix n n A ≃+* CStarMatrix n n A :=
  { ofMatrix with
    map_mul' := fun X Y => (of_mul_of X Y).symm
    map_add' := fun X Y => (of_add_of X Y).symm }

@[simp]
theorem ofMatrixNonUnitalRingEquiv_apply {A : Type uA} {n : Type uN}
    [Mul A] [AddCommMonoid A] [Fintype n] (X : Matrix n n A) :
    ofMatrixNonUnitalRingEquiv X = ofMatrix X := by
  rfl

@[simp]
theorem ofMatrixNonUnitalRingEquiv_symm_apply {A : Type uA} {n : Type uN}
    [Mul A] [AddCommMonoid A] [Fintype n] (X : CStarMatrix n n A) :
    ofMatrixNonUnitalRingEquiv.symm X = ofMatrix.symm X := by
  rfl

/-- Let `A` be an additive commutative monoid. Let `l` be an index type. Let `m` be a finite index type.
Let `n` be an index type. `A` has a multiplication. For `X : CStarMatrix l m A` and `Y : CStarMatrix
m n A`. Inverse rectangular multiplication transport, with the caller's existing operations.
-/
@[simp]
theorem ofMatrix_symm_mul {A : Type uA} {l : Type uL} {m : Type uM} {n : Type uN}
    [Mul A] [AddCommMonoid A] [Fintype m]
    (X : CStarMatrix l m A) (Y : CStarMatrix m n A) :
    ofMatrix.symm (X * Y) = ofMatrix.symm X * ofMatrix.symm Y := by
  apply (ofMatrix (m := l) (n := n) (A := A)).injective
  simpa only [Equiv.apply_symm_apply] using
    of_mul_of (ofMatrix.symm X) (ofMatrix.symm Y)

/-- Let `A` be a possibly nonunital ring. Let `n` be a finite index type. For `M : CStarMatrix n n A`
and `hM : IsIdempotentElem M`. Reflect idempotence by entries, without identifying independent Mul
records.
-/
theorem ofMatrix_symm_isIdempotent {A : Type uA} {n : Type uN}
    [NonUnitalRing A] [Fintype n]
    (M : CStarMatrix n n A) (hM : IsIdempotentElem M) :
    IsIdempotentElem (ofMatrix.symm M) := by
  change ofMatrix.symm M * ofMatrix.symm M = ofMatrix.symm M
  apply Matrix.ext
  intro i j
  have hentry := congrArg (fun T : CStarMatrix n n A => T i j) hM.eq
  change (∑ k : n, M i k * M k j) = M i j at hentry
  simpa only [Matrix.mul_apply, ofMatrix_symm_apply] using hentry

universe uR uO

/-- Let `R` be a semiring. Let `A` be a module over `R`. Let `m` be an index type. Let `n` be an index
type. Let `l` be an index type. Let `o` be a type. For `em : m ≃ l`, `en : n ≃ o`, `M : CStarMatrix
m n A`, `i : l` and `j : o`. Typed reindexing entries, avoiding a raw Matrix operation on the type
copy.
-/
theorem reindexₗ_apply_entry {R : Type uR} {A : Type uA}
    {m : Type uM} {n : Type uN} {l : Type uL} {o : Type uO}
    [Semiring R] [AddCommMonoid A] [Module R A]
    (em : m ≃ l) (en : n ≃ o) (M : CStarMatrix m n A) (i : l) (j : o) :
    reindexₗ R A em en M i j = M (em.symm i) (en.symm j) := by
  rfl

/-- Square `CStarMatrix` analogue of `Matrix.Semiring.isScalarTower`: scalars
acting entrywise associate through matrix multiplication.  Mathlib registers
the rectangular `CStarMatrix.instIsScalarTower`, but not this self-action
case needed for `Unitization.instSemiring` over a matrix algebra. -/
instance instIsScalarTowerSelf {R : Type*} {ι : Type*} {A : Type*}
    [Fintype ι] [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [IsScalarTower R A A] :
    IsScalarTower R (CStarMatrix ι ι A) (CStarMatrix ι ι A) :=
  inferInstanceAs <| IsScalarTower R (Matrix ι ι A) (Matrix ι ι A)

/-- Square `CStarMatrix` analogue of `Matrix.Semiring.smulCommClass`: scalars
acting entrywise commute with the left multiplication action of a matrix.
Mathlib registers the rectangular `CStarMatrix.instSMulCommClass`, but not
this self-action case needed for `Unitization.instSemiring` over a matrix
algebra. -/
instance instSMulCommClassSelf {R : Type*} {ι : Type*} {A : Type*}
    [Fintype ι] [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [SMulCommClass R A A] :
    SMulCommClass R (CStarMatrix ι ι A) (CStarMatrix ι ι A) :=
  inferInstanceAs <| SMulCommClass R (Matrix ι ι A) (Matrix ι ι A)

section Norm

open Finset
open scoped CStarAlgebra BigOperators

variable {A : Type uA} [NonUnitalCStarAlgebra A]
variable [PartialOrder A] [StarOrderedRing A]
variable {m : Type uM} {n : Type uN} [Fintype m] [Fintype n]

/-- Let `A` be a possibly nonunital complex C*-algebra with a compatible star order, and let `m`, `n` be
finite index types. For `M : CStarMatrix m n A`, the operator norm is bounded by the sum of the
norms of all its entries.
-/
theorem norm_le_sum_norm_entries (M : CStarMatrix m n A) :
    ‖M‖ ≤ ∑ j, ∑ i, ‖M i j‖ := by
  rw [norm_def]
  refine (toCLM M).opNorm_le_bound (by positivity) fun v => ?_
  simp only [toCLM_apply_eq_sum]
  calc
    ‖(WithCStarModule.equiv _ _).symm (fun j => ∑ i, v i * M i j)‖ ≤
        ∑ j, ‖∑ i, v i * M i j‖ := WithCStarModule.pi_norm_le_sum_norm _
    _ ≤ ∑ j, ∑ i, ‖v i * M i j‖ := Finset.sum_le_sum fun j _ => norm_sum_le _ _
    _ ≤ ∑ j, ∑ i, ‖v i‖ * ‖M i j‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ∑ j, ∑ i, ‖v‖ * ‖M i j‖ := by
      gcongr with j _ i _
      exact WithCStarModule.norm_apply_le_norm v i
    _ = (∑ j, ∑ i, ‖M i j‖) * ‖v‖ := by
      simp only [Finset.sum_mul, mul_comm]

end Norm

end CStarMatrix

end
