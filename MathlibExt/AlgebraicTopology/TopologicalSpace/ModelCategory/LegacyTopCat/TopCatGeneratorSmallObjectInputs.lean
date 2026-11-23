/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorPresentability

/-!
# Small-object structural inputs for realized TopCat generators

This file is part of the KQ3 layer. It supplies only the two missing
structural inputs for the eventual `IsCardinalForSmallObjectArgument` at
`realizedGeneratorCardinal`:

* an `OrderBot realizedGeneratorCardinal.ord.ToType` instance from
  nonzeroness via `WellFoundedLT.toOrderBot`;
* a `MorphismProperty.IsSmall` instance for the generator union
  `TopCat.realizedBoundaryInclusions ⊔ TopCat.realizedHornInclusions`
  from the existing component instances via `sup_eq_iSup` and
  `MorphismProperty.isSmall_iSup` over `Bool`.

This is not an `IsCardinalForSmallObjectArgument` instance, and not a
small-object, factorization, cofibration, weak-equivalence, or
model-structure claim.
-/

@[expose] public section

universe u

/-- The generator cardinal index type has a bottom element. -/
noncomputable instance : OrderBot realizedGeneratorCardinal.{u}.ord.ToType :=
  haveI : Nonempty realizedGeneratorCardinal.{u}.ord.ToType :=
    Ordinal.nonempty_toType_iff.mpr
      (by simpa using isRegular_realizedGeneratorCardinal.{u}.ne_zero)
  WellFoundedLT.toOrderBot realizedGeneratorCardinal.{u}.ord.ToType

/-- The generator union is small. -/
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
