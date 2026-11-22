/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OrthogonalGammaFaceReadback

/-!
# Original Diagram Pair

Complete source maps, coefficients and comparison morphisms for the original
orthogonal Gamma construction, retaining the full parameter and universe families.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe uV vV uI vI
open CategoryTheory MonoidalCategory CategoryTheory.EnrichedFunctorCat CategoryTheory.Limits
open CategoryTheory.Spectra CategoryTheory.Spectra.OrthogonalSourceRightModule
open PointedCGWH.Spectra.Orthogonal
open scoped MonoidalClosed
attribute [local instance] Enriched.prodCategory MonoidalLeftAction.monoidalOppositeLeftAction
  EnrichedDayKernel.ColimitMonoidal.smallestColimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.DayTensorBridge
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I] [EnrichedOrdinaryCategory V I]
  [HasColimitsOfSize.{uI, uI} V] (d : EnrichedMonoidalCategoryData V I)

/-- The entire original Day pair equals the same pair preceded by the original identity
tensor comparison; both Iso maps and every coefficient remain unchanged. -/
theorem original_diagram_pair_eq_comparison (n r : I) (K L : V) :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    EnrichedDayKernel.FreePairComparison.iso d.tensorEnrichedFunctor n r K L =
      (originalTensorComparison d).app (Free.object n K, Free.object r L) ≪≫
        EnrichedDayKernel.FreePairComparison.iso d.tensorEnrichedFunctor n r K L := by
  let := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
  apply Iso.ext
  change (EnrichedDayKernel.FreePairComparison.iso d.tensorEnrichedFunctor n r K L).hom =
    (originalTensorComparison d).hom.app (Free.object n K, Free.object r L) ≫
      (EnrichedDayKernel.FreePairComparison.iso d.tensorEnrichedFunctor n r K L).hom
  rw [(originalTensorComparison_components d (Free.object n K) (Free.object r L)).1]
  exact (Category.id_comp
    (EnrichedDayKernel.FreePairComparison.iso d.tensorEnrichedFunctor n r K L).hom).symm

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.DayTensorBridge

universe u v
attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
  OrthogonalIndex.enrichedOrdinaryCategory OrthogonalIndex.symmetricCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits

namespace PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
private local instance constructionMonoidal1 : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  :=
  OrthogonalDay.monoidalCategory.{u, v}

/-- The actual complete canonical source diagram-pair family has the same original Day
comparison before its same original free-pair Iso. -/
theorem native_diagram_pair_eq_original_comparison :
    SphereSmashFree.diagramPair.{u, v} =
      (fun n r K L => (DayTensorBridge.originalTensorComparison
        OrthogonalIndex.enrichedMonoidalData.{u, v}).app (Free.object n K, Free.object r L) ≪≫
        EnrichedDayKernel.FreePairComparison.iso
          OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor n r K L) := by
  funext n r K L
  exact DayTensorBridge.original_diagram_pair_eq_comparison
    OrthogonalIndex.enrichedMonoidalData.{u, v} n r K L

end PointedCGWH.Spectra.NativeStableMonoidal.OrthogonalGammaFaceReadback.PairCastBoundary
