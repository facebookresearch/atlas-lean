/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordLayerAnodyne
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordLayerColimit
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordZeroLayer
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Whole original enriched free-word attachments are Hom weak equivalences

The actual finite shape pushouts and the proved countable word colimit
identify the whole original Hom inclusion as an anodyne composite.
This includes arbitrary original loops and identities and all attached
words. The source need not be fibrant or cofibrant as an enrichment.
-/

noncomputable section
universe u
open CategoryTheory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C : FixedObjects O}

/-- The actual zero-layer inclusion is the same countable composite of the proved anodyne finite steps. -/
def layerAnodyneComposition (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) :
    SSet.anodyneExtensions.TransfiniteCompositionOfShape ℕ (layer T a b 0).ι where
  __ := zeroLayerComposition T a b
  map_mem n _hn := layerInclusion_anodyne T hi a b n

/-- The genuine entire zero-layer inclusion is anodyne by actual transfinite closure. -/
theorem zeroLayerInclusion_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) :
    SSet.anodyneExtensions (layer T a b 0).ι :=
  SSet.anodyneExtensions.transfiniteCompositionsOfShape_le ℕ _
    (MorphismProperty.TransfiniteCompositionOfShape.mem _ (layerAnodyneComposition T hi a b))

/-- Every actual original old Hom inclusion in the whole free-word attachment is anodyne. -/
theorem oldHom_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) :
    SSet.anodyneExtensions (oldHom T a b) := by
  rw [← zeroLayerHom_ι]
  exact SSet.anodyneExtensions.comp_mem _ _ (SSet.anodyneExtensions.of_isIso _)
    (zeroLayerInclusion_anodyne T hi a b)

/-- The actual whole original enriched attachment map has anodyne Hom maps at every original pair. -/
theorem homMap_oldMap_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) :
    SSet.anodyneExtensions (homMap (oldMap T) a b) := by
  rw [homMap_oldMap]
  exact oldHom_anodyne T hi a b

/-- These are genuine weak maps in the original scalar model on the same full Hom objects. -/
theorem homMap_oldMap_weak (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) (a b : O) :
    SSet.realizationWeakEquivalences (homMap (oldMap T) a b) := by
  have h := homMap_oldMap_anodyne T hi a b
  rw [SSet.anodyneExtensions_eq_trivialCofibrations] at h
  exact (weakEquivalence_iff _).mp ((mem_trivialCofibrations_iff _).mp h).2

/-- Every individual original source vertex and its entire actual enriched Hom map satisfy scalar weakness. -/
theorem oldMap_allOriginalHoms_weak (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y)) :
    ∀ a b : C.val, SSet.realizationWeakEquivalences ((oldMap T).val.map a b) :=
  (all_homMap_property_iff SSet.realizationWeakEquivalences (oldMap T)).mp
    (homMap_oldMap_weak T hi)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
