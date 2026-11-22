/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.GammaFaceBridge.OriginalSourceGetters

/-!
# Original Unit Evaluation

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open PointedCGWH.Spectra.Orthogonal
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaSmashFaces
open PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback
open scoped MonoidalClosed
attribute [local instance] SphereSmashStructure.indexCategory
  SphereSmashStructure.indexMonoidalCategory SphereSmashStructure.indexEnrichedOrdinaryCategory
  SphereSmashStructure.indexSymmetricCategory PointedCGWH.EnrichedMapping.hasSmallLimits
  Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
private local instance constructionMonoidal1 : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} :=
  CanonicalSourceSmash.monoidalCategory.{u, v}

/-- Native level evaluation preserves the entire original monoidal unit equality
cast as the original identity on the same complete unit level. -/
theorem original_native_unit_cast_evaluation_getter (r : ℕ) :
    (evaluation (CanonicalSourceFreeSmash.pairData.{u, v}.indexMap r)).map
      (eqToHom (congrArg
        (fun Z : MonoidalCategory CanonicalSourceSmash.Carrier.{u, v} => Z.tensorUnit)
        PointedCGWH.Spectra.NativeStableMonoidal.OriginalUnitLiftIntegerReadback.native_primitive_monoidal_eq.{u,
          v}.symm)) =
      𝟙 ((𝟙_ CanonicalSourceSmash.Carrier.{u, v}).toEnrichedFunctor.obj
        (CanonicalSourceFreeSmash.pairData.{u, v}.indexMap r)) := by
  rw [eqToHom_map]
  exact eqToHom_refl _ _

end PointedCGWH.Spectra.Orthogonal.NativeGammaFaceBridge
