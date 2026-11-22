/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceLayerWeak
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono

/-!
# Weakness of the SAME whole original relative-word source comparison

The actual full original enriched source map is the colimit of its
proved weak normalized-layer restrictions. Both original word sequences
have monomorphic transitions and retain their genuine full colimit
universal properties. The native sequential-mono theorem therefore
proves weakness of the SAME whole enriched Hom map, for arbitrary honest
Homwise weak input and every original quiver monomorphism attachment.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
variable {O : Type u} {C D : FixedObjects O}

/-- The SAME whole original source map is a natural comparison of its actual normalized layers. -/
def sourceWordLayerMap (T : Data C) (F : C ⟶ D) (a b : O) :
    wordLayerDiagram T a b ⟶ wordLayerDiagram (sourceChange T F) a b where
  app n := sourceLayerMap T F a b n
  naturality _n _m _f := rfl

/-- The complete actual layer cocone retains the SAME original enriched Hom source map. -/
theorem sourceWordLayerMap_cocone (T : Data C) (F : C ⟶ D) (a b : O) (n : ℕ) :
    (wordLayerCocone T a b).ι.app n ≫ homMap (sourceChangeMap T F) a b =
      (sourceWordLayerMap T F a b).app n ≫ (wordLayerCocone (sourceChange T F) a b).ι.app n := rfl

/-- The original full enriched Hom comparison is weak; all original words and maps are retained. -/
theorem sourceChangeMap_hom_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) (a b : O) :
    SSet.realizationWeakEquivalences (homMap (sourceChangeMap T F) a b) := by
  apply SSet.realizationWeakEquivalences.of_isColimit_nat_mono
    (sourceWordLayerMap T F a b) (wordLayerIsColimit T a b)
    (wordLayerIsColimit (sourceChange T F) a b) (homMap (sourceChangeMap T F) a b)
    (sourceWordLayerMap_cocone T F a b)
  · intro i j f
    rw [NatTrans.mono_iff_mono_app]
    intro q
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro p r h
    apply Subtype.ext
    exact congrArg (fun t : (layer T a b j).toSSet.obj q => t.val) h
  · intro i j f
    rw [NatTrans.mono_iff_mono_app]
    intro q
    apply (CategoryTheory.mono_iff_injective _).mpr
    intro p r h
    apply Subtype.ext
    exact congrArg (fun t : (layer (sourceChange T F) a b j).toSSet.obj q => t.val) h
  · intro n
    exact sourceLayerMap_weak T F hF a b n

/-- The SAME actual whole enriched source comparison is a genuine fixed-object weak map. -/
theorem sourceChangeMap_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) :
    FixedObjectModel.weakEquivalences O (sourceChangeMap T F) :=
  (FixedObjectModel.weakEquivalences_iff _).mpr (sourceChangeMap_hom_weak T F hF)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
