/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierColimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectOriginalIsomorphisms
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierReindexingEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectFilteredColimits

/-!
# The SAME original carrier colimit gives its genuine full fixed-label Hom colimits

The actual whole original carrier-colimit comparison and its object
function have genuine inverses. The SAME canonical reindexed projection
and original fixed-fiber reflection give the original fixed comparison
isomorphism. The complete original target cocone is thus colimiting,
and its full Hom evaluations retain genuine filtered colimits.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.CarrierColimit
open FixedObjects

variable {J : Type u} [Category.{u} J] (F : J ⥤ Carrier.{u}) (s : Cocone F) (hs : IsColimit s)
include hs

/-- The SAME genuine original whole carrier-colimit comparison with its actual inverse. -/
def originalIso : object F ≅ s.pt := IsColimit.coconePointUniqueUpToIso (isColimit F) hs

/-- Its full original forward functor is precisely the SAME original actual colimit descender. -/
theorem originalIso_hom : (originalIso F s hs).hom = desc F s := rfl

/-- The SAME whole original colimit descender is genuinely invertible. -/
theorem desc_isIso : IsIso (desc F s) := (originalIso F s hs).isIso_hom

/-- The actual original target-label function is bijective from the SAME genuine colimit comparison. -/
theorem targetLabels_bijective : Function.Bijective (targetLabels F s) := by
  let _ : IsIso (desc F s) := desc_isIso F s hs
  let _ : IsIso (forgetObjects.map (desc F s)) := inferInstance
  have h : Function.Bijective (desc F s).obj := (isIso_iff_bijective (forgetObjects.map (desc F s))).mp inferInstance
  exact (funext (desc_obj F s)) ▸ h

/-- The SAME canonical original object projection is a genuine whole enriched isomorphism. -/
theorem targetProjection_isIso : IsIso (CarrierReindexing.toTarget s.pt (targetLabels F s)) :=
  (CarrierReindexing.equivalenceIso s.pt (Equiv.ofBijective (targetLabels F s) (targetLabels_bijective F s
    hs))).isIso_hom

/-- The original full fixed-label comparison is genuinely invertible from its actual carrier inverse. -/
theorem fixedDesc_isIso : IsIso (fixedDesc F s) := by
  let _ : IsIso (fixedDesc F s).val :=
    @IsIso.of_isIso_comp_right Carrier.{u} inferInstance s.pt
      (CarrierReindexing.object s.pt (targetLabels F s)).val (object F)
      (fixedDesc F s).val (CarrierReindexing.toTarget s.pt (targetLabels F s))
      (targetProjection_isIso F s hs) (desc_isIso F s hs)
  exact isIso_of_original_isIso (fixedDesc F s)

/-- The SAME actual original target cocone has its genuine complete original fixed-label colimit property. -/
def targetCoconeIsColimit : IsColimit (targetCocone F s) := by
  apply IsColimit.ofIsoColimit (DiagramPresentation.isColimit (stages F))
  refine Cocone.ext (@asIso (FixedObjects (labelCocone F).pt) inferInstance
    (fixedObject F) (CarrierReindexing.object s.pt (targetLabels F s))
      (fixedDesc F s) (fixedDesc_isIso F s hs)) ?_
  intro j
  exact DiagramPresentation.desc_fac (stages F) (targetCocone F s) j

/-- Every SAME full original Hom cocone is genuinely colimiting for a filtered original carrier diagram. -/
def fullHomIsColimit [IsFiltered J] (x y : (labelCocone F).pt) :
    IsColimit ((FixedObjects.evaluation x y).mapCocone (targetCocone F s)) :=
  isColimitOfPreserves (FixedObjects.evaluation x y) (targetCoconeIsColimit F s hs)

end CategoryTheory.SimplicialEnrichment.CarrierColimit
