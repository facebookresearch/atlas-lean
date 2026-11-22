/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceChangeWeak
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual enriched source pushouts and genuine weak cobase changes

The unchanged target generators and original full attaching maps give
the complete original source-change pushout. Its weak map is therefore
the SAME actual cobase change of any genuine Homwise weak source map
along the original relative mono-quiver attachment. Every original
object label, Hom map and whole pushout leg is retained.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
variable {O : Type u} {C D : FixedObjects O}

/-- Composing the original whole attaching map gives the SAME source-changed attaching map. -/
theorem domainMap_sourceChange (T : Data C) (F : C ⟶ D) :
    domainMap T ≫ F = domainMap (sourceChange T F) := by
  apply FreeQuiver.generators_ext T.domain
  intro x y
  rw [homMap_comp, ← Category.assoc]
  change (FreeQuiver.generator T.domain x y ≫
      homMap (FreeQuiver.extend T.domain C T.attaching) x y) ≫ homMap F x y =
    FreeQuiver.generator T.domain x y ≫
      homMap (FreeQuiver.extend T.domain D (sourceChange T F).attaching) x y
  rw [FreeQuiver.generator_extend]
  exact (FreeQuiver.generator_extend (sourceChange T F).domain D
    (sourceChange T F).attaching x y).symm

/-- The SAME original free-target enriched map is retained by whole source change. -/
theorem newMap_sourceChangeMap (T : Data C) (F : C ⟶ D) :
    newMap T ≫ sourceChangeMap T F = newMap (sourceChange T F) := by
  apply FreeQuiver.generators_ext T.target
  intro x y
  rw [homMap_comp, ← Category.assoc]
  change (FreeQuiver.generator T.target x y ≫
      homMap (FreeQuiver.extend T.target (object T) (newHom T)) x y) ≫
      homMap (sourceChangeMap T F) x y =
    FreeQuiver.generator T.target x y ≫
      homMap (FreeQuiver.extend T.target (object (sourceChange T F)) (newHom (sourceChange T F))) x y
  rw [FreeQuiver.generator_extend]
  exact (newHom_sourceChangeMap T F x y).trans
    (FreeQuiver.generator_extend (sourceChange T F).target (object (sourceChange T F))
      (newHom (sourceChange T F)) x y).symm

/-- The original whole source-comparison square is genuinely a pushout of the original attachment. -/
theorem sourceChange_isPushout (T : Data C) (F : C ⟶ D) :
    IsPushout (oldMap T) F (sourceChangeMap T F) (oldMap (sourceChange T F)) := by
  have hp : IsPushout (domainMap T ≫ F) (targetMap T)
      (oldMap (sourceChange T F)) (newMap T ≫ sourceChangeMap T F) := by
    rw [domainMap_sourceChange, newMap_sourceChangeMap]
    exact isPushout (sourceChange T F)
  exact (hp.of_left (oldMap_sourceChangeMap T F).symm (isPushout T)).flip

/-- Any actual original cobase change along this mono-quiver attachment keeps its genuine weak source map. -/
theorem sourceChange_pushout_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) {P : FixedObjects O}
    (j : object T ⟶ P) (k : D ⟶ P) (hp : IsPushout (oldMap T) F j k) :
    FixedObjectModel.weakEquivalences O j := by
  let e := (sourceChange_isPushout T F).isoIsPushout _ _ hp
  have he : sourceChangeMap T F ≫ e.hom = j :=
    (sourceChange_isPushout T F).inl_isoIsPushout_hom _ _ hp
  have hw := (FixedObjectModel.weakEquivalences O).comp_mem _ _
    (sourceChangeMap_weak T F hF) ((FixedObjectModel.weakEquivalences O).of_isIso e.hom)
  exact he ▸ hw

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
