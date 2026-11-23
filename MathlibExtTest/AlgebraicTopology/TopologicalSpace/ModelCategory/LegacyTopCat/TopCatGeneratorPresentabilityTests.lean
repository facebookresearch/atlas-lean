/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatGeneratorPresentability

@[expose] public section

/-!
# TopCat generator presentability consumer tests

Minimal public client for `TopCatGeneratorPresentability`: `HasCardinalLT`
bounds, `Type`-level `IsCardinalPresentable`, and `IsSmall` generator
families. Not a `TopCat`-level presentability, small-object, factorization,
cofibration, weak-equivalence, or model-structure claim.
-/

set_option autoImplicit false

#check @hasCardinalLT_realizedBoundary
#check @hasCardinalLT_realizedHorn
#check @isCardinalPresentable_realizedBoundary
#check @isCardinalPresentable_realizedHorn
#check (inferInstance : CategoryTheory.MorphismProperty.IsSmall TopCat.realizedBoundaryInclusions)
#check (inferInstance : CategoryTheory.MorphismProperty.IsSmall TopCat.realizedHornInclusions)

example :
    HasCardinalLT ↥(SSet.toTop.{0}.obj (SSet.boundary.{0} 0))
      realizedGeneratorCardinal.{0} :=
  hasCardinalLT_realizedBoundary.{0} 0

example :
    HasCardinalLT
      ↥(SSet.toTop.{0}.obj (SSet.horn.{0} 0 ⟨0, Nat.zero_lt_succ 0⟩))
      realizedGeneratorCardinal.{0} :=
  hasCardinalLT_realizedHorn.{0} 0 ⟨0, Nat.zero_lt_succ 0⟩

example :
    CategoryTheory.IsCardinalPresentable
      ↥(SSet.toTop.{0}.obj (SSet.boundary.{0} 1))
      realizedGeneratorCardinal.{0} :=
  isCardinalPresentable_realizedBoundary.{0} 1

#print axioms hasCardinalLT_realizedBoundary
#print axioms hasCardinalLT_realizedHorn
#print axioms isCardinalPresentable_realizedBoundary
#print axioms isCardinalPresentable_realizedHorn
