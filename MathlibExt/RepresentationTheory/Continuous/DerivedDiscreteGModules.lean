/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective/Exactness.lean`,
lines 373–392 (AxiomMath/Stacks, revision `c496df0d9beea9deaeabcea8492605f9a0a2313b`); the source
file carries no individual copyright or author notice.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Modifications: the source composition is specialised to the discrete continuous integer-module
invariants functor, keeping the standard derived-category model used by the source's
`GroupCohomology/Continuous.lean`.
-/
module

public import MathlibExt.RepresentationTheory.Continuous.DiscreteGModules
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# The exact Axiom derived-invariants realization

This is the source's `rightDerivedPlus`: the degree-zero embedding into the
bounded below derived category, Mathlib's total right derived functor, then
degree-`n` homology. It is kept separate from the injective-resolution
realization in `DiscreteGModules.derivedCohomology`.
-/

@[expose] public noncomputable section

namespace DiscreteGModules

open CategoryTheory
open scoped DiscreteGModules

attribute [local instance] HasDerivedCategory.standard

/-- Axiom's exact higher derived invariants functor on its actual module category. -/
abbrev axiomDerivedCohomology (G : Type) [Group G] [TopologicalSpace G]
    [EnoughInjectives (ContinuousGModule.{0, 0} G)] (n : ℕ) :
    ContinuousGModule.{0, 0} G ⥤ AddCommGrpCat.{0} :=
  DerivedCategory.Plus.singleFunctor (ContinuousGModule.{0, 0} G) 0 ⋙
    (invariantsFunctor G).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (n : ℤ)

end DiscreteGModules
