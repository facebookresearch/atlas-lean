/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.ChevalleyEilenberg.CoalgebraWorkingHeight

/-!
# Functorial lifting of Chevalley–Eilenberg chain maps

Let `R` be a commutative ring and let `f : L → L'` be a Lie homomorphism between carriers in a
common universe. The lifted canonical CE map agrees with applying the module universe-lift
functor degreewise to the canonical CE chain map.

In every degree the exterior-power component is lifted by `up`, with the same ground action
and signed differential.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v z

namespace ChevalleyEilenberg

variable (R : Type u) [CommRing R] (L : Type v) [LieRing L] [LieAlgebra R L]
  {L' : Type v} [LieRing L'] [LieAlgebra R L']

/-- The lifted CE map as a module-functor image.

For a Lie homomorphism in a common carrier universe, the chosen-height CE chain map equals the
image of the canonical chain map under the module lift functor. -/
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
