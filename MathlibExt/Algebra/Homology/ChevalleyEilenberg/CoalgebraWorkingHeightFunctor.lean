/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraWorkingHeight

/-!
# Universe lifting of Chevalley–Eilenberg maps

For Lie algebras in a common carrier universe, lifting the Chevalley–Eilenberg chain map
agrees with applying the module universe-lift functor. The ground ring and the signed
differential are unchanged.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v z

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  {L' : Type v} [LieRing L'] [LieAlgebra R L']

/-- The working-height CE map equals the module-lift functor map. -/
theorem nativeLiftedComplexMapAtHeight_eq_uliftMap (f : L →ₗ⁅R⁆ L') :
    nativeLiftedComplexMapAtHeight.{u,v,v,z} R L f =
      ((ModuleCat.uliftFunctor.{max u v z, max u v} R).mapHomologicalComplex
        (ComplexShape.down ℕ)).map (nativeComplexMap R L f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rcases x with ⟨x⟩
  have h := nativeLiftedComplexMapAtHeight_f_up.{u,v,v,z} R L f n x
  change ((nativeLiftedComplexMapAtHeight.{u,v,v,z} R L f).f n).hom (ULift.up x) =
    ULift.up (((nativeComplexMap R L f).f n).hom x)
  rw [nativeComplexMap_f]
  exact h

end ChevalleyEilenberg
