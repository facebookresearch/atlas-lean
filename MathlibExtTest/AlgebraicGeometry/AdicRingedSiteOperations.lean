/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicRingedSiteOperations

/-!
# Tests for operations on modules over the continuous coefficient ring

The ring maps act on sections by precomposition and by applying the coefficient map; coefficient
change is functorial; the unit maps are adjoint; an exact inverse image has invertible derived
unit, found by instance search; cohomology maps are functorial.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExtTest.AlgebraicGeometry.AdicRingedSiteOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme
open MathlibExt.AlgebraicGeometry
open AdicRingedSiteOperations ContinuousAdicRingModules
open ProEtaleCohomologyFunctoriality

attribute [local instance] HasDerivedCategory.standard

variable (E F : Type) [CommRing E] [TopologicalSpace E]
  [IsTopologicalRing E] [CommRing F] [TopologicalSpace F]
  [IsTopologicalRing F]

example {Y X : Scheme} (f : Y ⟶ X) (U : X.ProEtᵒᵖ)
    (a : C(U.unop.left, ULift.{1} E))
    (x : (Limits.pullback U.unop.hom f : Scheme)) :
    (show C((Limits.pullback U.unop.hom f : Scheme), ULift.{1} E) from
      (coefficientPushforward E f).hom.app U a) x =
        a ((Limits.pullback.fst U.unop.hom f).base.hom x) := rfl

example {Y X : Scheme} (f : Y ⟶ X) (U : X.ProEtᵒᵖ)
    (a : (coefficientRing E X).obj.obj U) :
    (unitPushforward E f).val.app U a =
      (coefficientPushforward E f).hom.app U a := rfl

example (α : E →+* F) (hα : Continuous α) (X : Scheme)
    (U : X.ProEtᵒᵖ) (a : C(U.unop.left, ULift.{1} E))
    (x : U.unop.left) :
    (show C(U.unop.left, ULift.{1} F) from
      (coefficientMap E F α hα X).hom.app U a) x =
        ULift.up (α (a x).down) := rfl

example {Y X : Scheme} (f : Y ⟶ X)
    [(AdicRingedSiteOperations.pushforward E f).IsRightAdjoint] :
    (pullbackPushforwardAdjunction E f).homEquiv _ _ (unitPullback E f) =
      unitPushforward E f := unitPullback_mate E f

/-- Coefficient change along the identity is the identity. -/
example (X : Scheme) : coefficientMap E E (RingHom.id E) continuous_id X = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  ext U a
  rfl

/-- Coefficient change is compatible with composition. -/
example (G : Type) [CommRing G] [TopologicalSpace G] [IsTopologicalRing G] (α : E →+* F)
    (hα : Continuous α) (β : F →+* G) (hβ : Continuous β) (X : Scheme) :
    coefficientMap E G (β.comp α) (hβ.comp hα) X =
      coefficientMap E F α hα X ≫ coefficientMap F G β hβ X := by
  apply ObjectProperty.hom_ext
  ext U a
  rfl

/-- An inverse image preserving finite limits has invertible derived unit, by instance search. -/
example {Y X : Scheme} (f : Y ⟶ X) [(AdicRingedSiteOperations.pushforward E f).IsRightAdjoint]
    [PreservesFiniteLimits (AdicRingedSiteOperations.pullback E f)]
    [EnoughInjectives (AdicRingedSiteOperations.ModuleSheaf E X)]
    (K : AdicRingedSiteOperations.Cochains E X) :
    IsIso ((AdicRingedSiteOperations.pullback E f).rightDerivedFunctorPlusUnit.app K) :=
  inferInstance

/-- Cohomology maps are functorial. -/
example (X : Scheme) [EnoughInjectives (AdicRingedSiteOperations.ModuleSheaf E X)]
    {K L M : AdicRingedSiteOperations.Derived E X} (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    cohomologyMap E X (f ≫ g) n = cohomologyMap E X f n ≫ cohomologyMap E X g n :=
  _root_.CategoryTheory.Functor.map_comp _ f g

example (X : Scheme) [EnoughInjectives (AdicRingedSiteOperations.ModuleSheaf E X)]
    (K : AdicRingedSiteOperations.Derived E X) (n : ℤ) :
    cohomologyMap E X (𝟙 K) n = 𝟙 _ :=
  _root_.CategoryTheory.Functor.map_id _ K

end MathlibExtTest.AlgebraicGeometry.AdicRingedSiteOperations
