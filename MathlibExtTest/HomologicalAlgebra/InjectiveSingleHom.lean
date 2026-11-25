/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import MathlibExt.HomologicalAlgebra.InjectiveSingleHom
public import MathlibExt.HomologicalAlgebra.RightDerivedCohomology

@[expose] public section

/-! # Tests for `MathlibExt.HomologicalAlgebra` -/

noncomputable section

open CategoryTheory
open MathlibExt.HomologicalAlgebra.InjectiveSingleHom.DerivedCategory
open MathlibExt.HomologicalAlgebra.RightDerivedCohomology

namespace MathlibExtTest.HomologicalAlgebra

attribute [local instance] HasDerivedCategory.standard

/-- Morphisms into an injective object in degree `i` are morphisms out of
degree-`i` cohomology, linearly. -/
example (X : DerivedCategory (ModuleCat.{0} ℚ)) (E : ModuleCat.{0} ℚ) [Injective E] (i : ℤ) :
    (X ⟶ (DerivedCategory.singleFunctor (ModuleCat.{0} ℚ) i).obj E) ≃ₗ[ℚ]
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) i).obj X ⟶ E) :=
  homToInjectiveSingleLinearEquiv ℚ X E i

/-- The cohomology of the bounded-below derived functor on an object is its
classical right derived functor. -/
example (X : ModuleCat.{0} ℚ) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℚ) (n : ℤ)).obj
      (((𝟭 (ModuleCat.{0} ℚ)).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).obj
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{0} ℚ) 0).obj X)) ≅
      ((𝟭 (ModuleCat.{0} ℚ)).rightDerived n).obj X :=
  derivedCohomologyIso (𝟭 (ModuleCat.{0} ℚ)) X n

end MathlibExtTest.HomologicalAlgebra

end
