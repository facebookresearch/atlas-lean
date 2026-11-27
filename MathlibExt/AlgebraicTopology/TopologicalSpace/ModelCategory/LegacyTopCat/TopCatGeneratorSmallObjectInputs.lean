/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorPresentability

/-!
# Ordinal and family smallness for realized generators

The ordinal of the regular realized-generator cardinal has a bottom element.
The union of the realized boundary and horn inclusion families is small, since
both component families are small and the union is indexed by a finite type.
-/

@[expose] public section

universe u

/--
The ordinal index type of the realized-generator cardinal has a bottom element.
-/
noncomputable instance : OrderBot realizedGeneratorCardinal.{u}.ord.ToType :=
  haveI : Nonempty realizedGeneratorCardinal.{u}.ord.ToType :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa using isRegular_realizedGeneratorCardinal.{u}.ne_zero)
  WellFoundedLT.toOrderBot realizedGeneratorCardinal.{u}.ord.ToType

/--
The union of the realized boundary and realized horn inclusion families is
small in the space universe.
-/
instance : CategoryTheory.MorphismProperty.IsSmall.{u}
    (TopCat.realizedBoundaryInclusions.{u} ⊔ TopCat.realizedHornInclusions.{u}) := by
  rw [sup_eq_iSup]
  have hBool : Small.{u} Bool := small_zero Bool
  have hCases : ∀ b : Bool, CategoryTheory.MorphismProperty.IsSmall.{u}
      (cond b TopCat.realizedBoundaryInclusions.{u}
        TopCat.realizedHornInclusions.{u}) := by
    intro b
    cases b <;> simp only [Bool.cond_true, Bool.cond_false] <;> infer_instance
  exact @CategoryTheory.MorphismProperty.isSmall_iSup _ _ _ _ hBool hCases
