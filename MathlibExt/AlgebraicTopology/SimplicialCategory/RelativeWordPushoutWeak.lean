/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordAttachmentWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordPushout

/-!
# Actual enriched free-quiver pushouts have weak old Hom maps

The proved whole word pushout compares with any actual pushout of the
same original span. This comparison fixes the original labels and every
map. Scalar anodyne closure transfers the proved entire attachment
weakness to that same enriched pushout, including its canonical legs.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C : FixedObjects O}

/-- Compare the constructed whole word object with an actual pushout of the same original enriched span. -/
def pushoutComparison (T : Data C) {D : FixedObjects O} (j : C ⟶ D)
    (k : FreeQuiver.object T.target ⟶ D)
    (hp : IsPushout (domainMap T) (targetMap T) j k) : object T ≅ D :=
  (isPushout T).isoIsPushout _ _ hp

/-- The entire original old enriched map is the same actual pushout leg under the comparison. -/
theorem oldMap_pushoutComparison (T : Data C) {D : FixedObjects O} (j : C ⟶ D)
    (k : FreeQuiver.object T.target ⟶ D)
    (hp : IsPushout (domainMap T) (targetMap T) j k) :
    oldMap T ≫ (pushoutComparison T j k hp).hom = j :=
  (isPushout T).inl_isoIsPushout_hom _ _ hp

/-- The entire original free-target map is the same actual second pushout leg. -/
theorem newMap_pushoutComparison (T : Data C) {D : FixedObjects O} (j : C ⟶ D)
    (k : FreeQuiver.object T.target ⟶ D)
    (hp : IsPushout (domainMap T) (targetMap T) j k) :
    newMap T ≫ (pushoutComparison T j k hp).hom = k :=
  (isPushout T).inr_isoIsPushout_hom _ _ hp

/-- Any actual pushout of the same anodyne free-quiver span has the same anodyne original old Hom maps. -/
theorem pushout_leftHom_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y))
    {D : FixedObjects O} (j : C ⟶ D) (k : FreeQuiver.object T.target ⟶ D)
    (hp : IsPushout (domainMap T) (targetMap T) j k) (x y : O) :
    SSet.anodyneExtensions (homMap j x y) := by
  let e := pushoutComparison T j k hp
  let _ : IsIso (homMap e.hom x y) :=
    inferInstanceAs (IsIso ((evaluation x y).map e.hom))
  have h := SSet.anodyneExtensions.comp_mem _ _ (homMap_oldMap_anodyne T hi x y)
    (SSet.anodyneExtensions.of_isIso (homMap e.hom x y))
  rw [← homMap_comp, oldMap_pushoutComparison] at h
  exact h

/-- The actual canonical enriched free-quiver pushout leg has anodyne maps on every same original Hom. -/
theorem canonicalPushout_leftHom_anodyne (T : Data C)
    [HasPushout (domainMap T) (targetMap T)]
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (x y : O) :
    SSet.anodyneExtensions (homMap (pushout.inl (domainMap T) (targetMap T)) x y) :=
  pushout_leftHom_anodyne T hi _ _ (IsPushout.of_hasPushout _ _) x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
