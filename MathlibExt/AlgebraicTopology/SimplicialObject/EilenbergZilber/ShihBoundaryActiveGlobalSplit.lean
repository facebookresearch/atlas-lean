/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryPositiveReindex
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.ShihBoundaryActiveDecomposition

/-!
# Global mixed/nonmixed split of the active Shih coordinates

This file applies the shuffle-boundary predicate directly to
`ShihUpperActiveData`, the canonical coordinates for active upper boundary
faces. Fixed-bidegree cancellation and nonmixed reindexing remain in
`ShihBoundaryActiveDecomposition`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory MonoidalCategory Simplicial
open scoped MonoidalCategory

universe v u

namespace AlgebraicTopology.EilenbergZilber

def ShihUpperActiveData.IsMixed {n : ℕ}
    (z : ShihUpperActiveData n) : Prop :=
  Shuffle.IsMixedBoundary z.1.shuffle z.2

abbrev ShihUpperMixedData (n : ℕ) :=
  {z : ShihUpperActiveData n // z.IsMixed}

abbrev ShihUpperNonmixedData (n : ℕ) :=
  {z : ShihUpperActiveData n // ¬z.IsMixed}

noncomputable instance (n : ℕ) :
    DecidablePred (@ShihUpperActiveData.IsMixed n) :=
  Classical.decPred _

noncomputable instance (n : ℕ) : Fintype (ShihUpperMixedData n) := by
  classical
  exact Subtype.fintype _

noncomputable instance (n : ℕ) : Fintype (ShihUpperNonmixedData n) := by
  classical
  exact Subtype.fintype _

/-- The canonical active coordinates split exactly according to whether the
local face is a mixed shuffle boundary. -/
noncomputable def shihUpperActiveDataEquivMixedSumNonmixed (n : ℕ) :
    ShihUpperActiveData n ≃
      ShihUpperMixedData n ⊕ ShihUpperNonmixedData n :=
  (Equiv.sumCompl ShihUpperActiveData.IsMixed).symm

/-- Sum form of the global mixed/nonmixed split. -/
theorem sum_shihUpperActiveData_eq_mixed_add_nonmixed
    {A : Type*} [AddCommMonoid A] (n : ℕ)
    (f : ShihUpperActiveData n → A) :
    ∑ z, f z =
      (∑ z : ShihUpperMixedData n, f z.val) +
        ∑ z : ShihUpperNonmixedData n, f z.val := by
  classical
  exact (Fintype.sum_subtype_add_sum_subtype
    ShihUpperActiveData.IsMixed f).symm

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]

/-- The upper boundary term represented by an active-data coordinate. -/
def shihUpperActiveDataTerm (X Y : SimplicialObject C) {n : ℕ}
    (z : ShihUpperActiveData n) :=
  let w := (shihUpperPositiveActiveEquiv n).symm z
  shihUpperBoundaryTerm X Y (n + 1) w.val.val.1 w.val.val.2.succ

/-- The canonical active boundary sum is the sum of its mixed and nonmixed
subfamilies. -/
theorem shihUpperActiveData_sum_eq_mixed_add_nonmixed
    (X Y : SimplicialObject C) (n : ℕ) :
    ∑ z : ShihUpperActiveData n, shihUpperActiveDataTerm X Y z =
      (∑ z : ShihUpperMixedData n,
        shihUpperActiveDataTerm X Y z.val) +
      ∑ z : ShihUpperNonmixedData n,
        shihUpperActiveDataTerm X Y z.val :=
  sum_shihUpperActiveData_eq_mixed_add_nonmixed n
    (shihUpperActiveDataTerm X Y)

end AlgebraicTopology.EilenbergZilber
