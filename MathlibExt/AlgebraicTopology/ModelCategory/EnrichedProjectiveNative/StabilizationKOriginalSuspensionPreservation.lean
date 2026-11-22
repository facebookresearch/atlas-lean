/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKScalarTestPreservation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarSphereSuspensionComparison

/-!
# Original I suspension preserves the full Omega tests after Q

The literal original suspension and scalar sphere suspension are naturally
isomorphic in the original level homotopy category. Transport the proved
scalar tests through that constructed comparison at every original Omega target.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK

variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (s : NativeStabilizationFamily.{u, v} I L)
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I
attribute [local instance] Native.modelCategory

/-- Original I suspension after Q preserves every original Omega-target test. -/
theorem originalISuspensionQMap_omegaTests {X Y : D (I := I)} (f : X ⟶ Y)
    (hf : omegaTests s f) :
    omegaTests s ((OriginalISuspension.suspension (B := B)).map
      ((Replacement.cofibrantReplacement (B := B)).map f)) := by
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  have hScalar := tensorQMap_omegaTests (B := B) s PointedCGWH.sphereOne f hf
  intro E hE
  let H := toHomotopyCategory (D (I := I))
  let e := ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B) (I := I)
  let W : MorphismProperty (HomotopyCategory (D (I := I))) :=
    ((MorphismProperty.isomorphisms (Type (v + 1))).inverseImage (yoneda.obj (H.obj E))).unop
  have hT : W (H.map ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map
      ((Replacement.cofibrantReplacement (B := B)).map f))) := by
    change IsIso ((yoneda.obj (H.obj E)).map
      (H.map ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map
        ((Replacement.cofibrantReplacement (B := B)).map f))).op)
    exact (isIso_iff_bijective _).mpr (hScalar E hE)
  let a : Arrow.mk (H.map ((OriginalISuspension.suspension (B := B)).map
      ((Replacement.cofibrantReplacement (B := B)).map f))) ≅
      Arrow.mk (H.map ((EnrichedFunctorCat.tensorLeft PointedCGWH.sphereOne).map
        ((Replacement.cofibrantReplacement (B := B)).map f))) :=
    Arrow.isoMk (e.app X) (e.app Y)
      (ScalarSphereSuspension.originalISuspensionQIsoSphereQ_hom_naturality (B := B) f).symm
  have hI := (W.arrow_mk_iso_iff a).mpr hT
  exact (isIso_iff_bijective _).mp hI

end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
