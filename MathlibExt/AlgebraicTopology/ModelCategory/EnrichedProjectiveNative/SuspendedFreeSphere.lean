/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.FreeSphereHom
import MathlibExt.CategoryTheory.Enriched.ScalarFreeTensor
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ScalarSphereSuspensionComparison
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKOriginalSuspensionPreservation

/-!
# Original suspended free-sphere comparisons

The actual scalar/free associator compares complete free diagrams. The
original I suspension after Q reaches the same scalar free sphere through
its actual natural suspension comparison and the scalar image of the Q
counit. The latter is weak by the original scalar Quillen pair on the
proved cofibrant free source.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open scoped CGWH.modelCategory
namespace HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
open CategoryTheory.EnrichedFunctorCat
attribute [local instance] Native.modelCategory Native.allObjectsFibrant
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
  {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
private abbrev H := toHomotopyCategory (EnrichedFunctorCat PointedCGWH.{u, v} I)
private abbrev Q := Replacement.cofibrantReplacement (B := B) (A := I)
private abbrev ε := Replacement.cofibrantReplacementCounit (B := B) (A := I)

/-- Scalar tensor of an original free coefficient is the full original
suspended free coefficient. -/
def scalarFreeCoefficientIso (a : I) (K : PointedCGWH.{u, v}) :
    tensorLeftObject PointedCGWH.sphereOne (Free.object a K) ≅
      Free.object a (PointedCGWH.suspension.obj K) :=
  Free.scalarFreeIso PointedCGWH.sphereOne K a

/-- Original scalar suspension of a free sphere uses the same complete coefficient comparison. -/
abbrev scalarFreeSphereIso (a : I) (n : ℕ) :=
  scalarFreeCoefficientIso a (PointedCGWH.SphereHom.sphere.{u, v} n)

/-- The original I suspension after Q of a free sphere retains the actual scalar/free comparison. -/
def originalSuspendedFreeSphereIso (a : I) (n : ℕ) :
    H.obj (OriginalISuspension.suspension (B := B) |>.obj
      (Q.obj (Free.object a (PointedCGWH.SphereHom.sphere n)))) ≅
      H.obj (Free.object a (PointedCGWH.suspension.obj (PointedCGWH.SphereHom.sphere n))) := by
  let T := EnrichedFunctorCat.tensorLeft (A := I) PointedCGWH.sphereOne
  let X := Free.object a (PointedCGWH.SphereHom.sphere n)
  let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
    PointedCGWH.modelCategory.sphereOne_isCofibrant
  let _ : (ScalarLeibniz.adjunction (A := I) PointedCGWH.sphereOne).IsQuillenAdjunction :=
    ScalarCompatibility.scalar_isQuillen PointedCGWH.sphereOne
  let _ : IsCofibrant (PointedCGWH.SphereHom.sphere.{u, v} n) := sphere_isCofibrant n
  let _ : (Free.adjunction (V := PointedCGWH.{u, v}) a).IsQuillenAdjunction :=
    Native.freeAtEvaluation_isQuillenAdjunction a
  let _ : IsCofibrant X :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := Free.adjunction a)
      inferInstance
  let _ : IsCofibrant ((𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj X) :=
    (inferInstance : IsCofibrant X)
  let _ : IsCofibrant (Q.obj X) := Replacement.isCofibrant_cofibrantReplacement X
  let _ : WeakEquivalence (ε.app X) :=
    (weakEquivalence_iff _).mpr (Replacement.cofibrantReplacementCounit_mem_weakEquivalences X)
  have hT : WeakEquivalence (T.map (ε.app X)) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := ScalarLeibniz.adjunction PointedCGWH.sphereOne) (ε.app X)
  exact (ScalarSphereSuspension.originalISuspensionQIsoSphereQ (B := B)).app X ≪≫
    Localization.Construction.wIso (T.map (ε.app X)) hT.mem ≪≫
      H.mapIso (scalarFreeSphereIso a n)

omit B in
/-- Every original coefficient arrow retains the whole scalar/free comparison square. -/
theorem scalarFreeCoefficientIso_naturality (a : I) {K K' : PointedCGWH.{u, v}} (f : K ⟶ K') :
    tensorLeftMap PointedCGWH.sphereOne ((Free.functor a).map f) ≫
        (scalarFreeCoefficientIso a K').hom =
      (scalarFreeCoefficientIso a K).hom ≫
        (Free.functor a).map (PointedCGWH.sphereOne ◁ f) :=
  Free.scalarFreeIso_coefficient PointedCGWH.sphereOne a f

end HomotopicalAlgebra.EnrichedProjective.Native.FreeSphereHom
