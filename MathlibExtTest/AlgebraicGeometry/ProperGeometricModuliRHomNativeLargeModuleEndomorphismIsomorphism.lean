/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ProperGeometricModuliRHomNativeLargeModuleEndomorphismIsomorphism

@[expose] public section

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry

namespace ProperGeometricModuliRHomNativeLargeModuleEndomorphismIsomorphism

universe u

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
open WantedExt.AlgebraicGeometry.ProperGeometricModuliRHomWanted

/-- Each degree of the endomorphism map is an isomorphism. -/
example (k : Type u) [CommRing k] (UL : CochainLiftModel k) (T : DGCat k)
    (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M) (n : ℤ) :
    IsIso (ML.endomorphismMap.f n) := by
  have := native_large_module_endomorphism_isomorphism k UL T M ML
  infer_instance

/-- The endomorphism map has a two-sided inverse. -/
example (k : Type u) [CommRing k] (UL : CochainLiftModel k) (T : DGCat k)
    (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M) :
    ∃ g, ML.endomorphismMap ≫ g = 𝟙 _ ∧ g ≫ ML.endomorphismMap = 𝟙 _ := by
  have := native_large_module_endomorphism_isomorphism k UL T M ML
  exact ⟨inv ML.endomorphismMap, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

/-- The degree-zero component of the endomorphism map acts bijectively. -/
example (k : Type u) [CommRing k] (UL : CochainLiftModel k) (T : DGCat k)
    (M : RightModule k T) (ML : LargeProjectiveModuleLift UL T M) :
    Function.Bijective (ML.endomorphismMap.f 0) := by
  have := native_large_module_endomorphism_isomorphism k UL T M ML
  exact ConcreteCategory.bijective_of_isIso _

end ProperGeometricModuliRHomNativeLargeModuleEndomorphismIsomorphism

end MathlibExtTest.AlgebraicGeometry
