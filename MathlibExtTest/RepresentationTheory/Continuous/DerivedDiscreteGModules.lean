/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.RepresentationTheory.Continuous.DerivedDiscreteGModules

/-!
# The bounded-below derived realization of discrete invariants

`axiomDerivedCohomology` is the composite of the degree-zero embedding into
the bounded-below derived category, the total right derived functor of the
invariants, and degree-`n` homology, for the standard derived category. Its
total derived functor is triangulated and the composite is additive.
-/

noncomputable section

open CategoryTheory DiscreteGModules
open scoped DiscreteGModules

namespace MathlibExtTest.DerivedDiscreteGModules

attribute [local instance] HasDerivedCategory.standard

variable (G : Type) [Group G] [TopologicalSpace G]
  [EnoughInjectives (ContinuousGModule.{0, 0} G)]

example (n : ℕ) : axiomDerivedCohomology G n =
    DerivedCategory.Plus.singleFunctor (ContinuousGModule.{0, 0} G) 0 ⋙
      (invariantsFunctor G).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (n : ℤ) := rfl

example : (invariantsFunctor G).rightDerivedFunctorPlus.IsTriangulated := inferInstance

instance (n : ℕ) : (axiomDerivedCohomology G n).Additive :=
  inferInstanceAs (DerivedCategory.Plus.singleFunctor (ContinuousGModule.{0, 0} G) 0 ⋙
      (invariantsFunctor G).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{0} (n : ℤ)).Additive

example (n : ℕ) (M N : ContinuousGModule.{0, 0} G) (f g : M ⟶ N) :
    (axiomDerivedCohomology G n).map (f + g) =
      (axiomDerivedCohomology G n).map f + (axiomDerivedCohomology G n).map g :=
  (axiomDerivedCohomology G n).map_add

end MathlibExtTest.DerivedDiscreteGModules
