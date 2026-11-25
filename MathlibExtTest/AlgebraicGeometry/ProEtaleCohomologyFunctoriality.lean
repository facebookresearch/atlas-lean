/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality

/-! # Tests for functoriality of pro-étale cohomology

Base change between small pro-étale sites is continuous and representably flat; inverse image is
left adjoint to direct image and exact; cohomology is an `R`-module; the inverse image of the
constant sheaf is the constant sheaf; the cohomology maps are additive.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.ProEtaleCohomologyFunctoriality

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ContinuousAdicCoefficients
open MathlibExt.AlgebraicGeometry.ProEtaleCohomologyFunctoriality

universe u

variable {Y X : Scheme.{u}} (f : Y ⟶ X) (R : Type) [CommRing R]

example : PreservesFiniteLimits (baseChange f) := inferInstance

example : RepresentablyFlat (baseChange f) := inferInstance

example : (baseChange f).IsContinuous (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) :=
  inferInstance

example : pullback R f ⊣ pushforward R f := pullbackAdjunction R f

/-- Inverse image is exact. -/
example : PreservesFiniteLimits (pullback R f) ∧ PreservesFiniteColimits (pullback R f) :=
  ⟨inferInstance, inferInstance⟩

example : (pullback R f).obj (constantUnit R X) ≅ constantUnit R Y := constantPullbackIso R f

example (F : CoefficientSheaf X R) (n : ℕ) : Module R (Cohomology R X F n) := inferInstance

example {F : CoefficientSheaf X R} {G : CoefficientSheaf Y R} (c : (pullback R f).obj F ⟶ G)
    (n : ℕ) (a b : Cohomology R X F n) :
    cohomologyPullback R f c n (a + b) =
      cohomologyPullback R f c n a + cohomologyPullback R f c n b :=
  map_add _ a b

open CategoryTheory.Abelian in
/-- In degree zero, the cohomology map sends the class of `a : R ⟶ F` to the class of the
composite `R ≅ f⁻¹ R ⟶ f⁻¹ F ⟶ G`; this rules out an identically zero construction. -/
example {F : CoefficientSheaf X R} {G : CoefficientSheaf Y R} (c : (pullback R f).obj F ⟶ G)
    (a : constantUnit R X ⟶ F) :
    cohomologyPullback R f c 0 (Ext.mk₀ a) =
      Ext.mk₀ ((constantPullbackIso R f).inv ≫ (pullback R f).map a ≫ c) := by
  change (Ext.mk₀ (constantPullbackIso R f).inv).comp
    (((Ext.mk₀ a).mapExactFunctor (pullback R f)).comp (Ext.mk₀ c) rfl) rfl = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]

section ContinuousCoefficients

variable (M : Type (u + 1)) [TopologicalSpace M] [AddCommGroup M] [Module R M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

/-- The inverse-image coefficient map is the adjoint of precomposition with the projection. -/
example : coefficientPullback R M f =
    ((pullbackAdjunction R f).homEquiv _ _).symm (coefficientPushforward R M f) := rfl

example (n : ℕ) :
    continuousCohomologyPullback R M f n = cohomologyPullback R f (coefficientPullback R M f) n :=
  rfl

end ContinuousCoefficients

end MathlibExtTest.AlgebraicGeometry.ProEtaleCohomologyFunctoriality
