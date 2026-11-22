/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardAdjunction
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModel
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenAdjunction

/-!
# The SAME actual arbitrary-label pushforward is a genuine Quillen adjunction

The existing whole pushforward and label-restriction functors retain
all original object images, full Hom maps, generators, unit and counit.
Restriction preserves the actual original Hom weak and Kan-fibration
classes at those SAME images. The genuine fixed-object model lifting
systems therefore make the existing adjunction Quillen, for arbitrary
label maps including empty and colliding images.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction
variable {A O : Type u} (a : A → O)

/-- The SAME original restricted Hom maps preserve the genuine original Homwise weak class. -/
theorem map_weak {C D : FixedObjects O} (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) :
    FixedObjectModel.weakEquivalences A ((functor a).map F) := by
  apply (FixedObjectModel.weakEquivalences_iff _).mpr
  intro s t
  have h := (FixedObjectModel.weakEquivalences_iff F).mp hF (a s) (a t)
  exact (congrArg (fun f : hom C (a s) (a t) ⟶ hom D (a s) (a t) =>
    SSet.realizationWeakEquivalences f) (homMap_map a F s t)).mpr h

/-- Restriction preserves the SAME full original Kan-fibration maps at every original image pair. -/
theorem map_fibration {C D : FixedObjects O} (F : C ⟶ D)
    (hF : FixedObjectModel.fibrations O F) :
    FixedObjectModel.fibrations A ((functor a).map F) := by
  apply (FixedObjectModel.fibrations_iff _).mpr
  intro s t
  have h := (FixedObjectModel.fibrations_iff F).mp hF (a s) (a t)
  exact (congrArg (fun f : hom C (a s) (a t) ⟶ hom D (a s) (a t) =>
    Fibration f) (homMap_map a F s t)).mpr h

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelRestriction

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
variable {A O : Type u} (a : A → O)
attribute [local instance] FixedObjectModel.modelCategory

/-- The SAME actual original pushforward/restriction adjunction is genuinely Quillen for every label map. -/
instance quillenAdjunction : Adjunction.IsQuillenAdjunction (adjunction a) := by
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro C D F hF
    exact LabelRestriction.map_fibration a F hF
  · intro C D F hF
    change FixedObjectModel.fibrations A ((LabelRestriction.functor a).map F) ∧
      FixedObjectModel.weakEquivalences A ((LabelRestriction.functor a).map F)
    exact ⟨LabelRestriction.map_fibration a F hF.1, LabelRestriction.map_weak a F hF.2⟩

/-- The original whole pushed map of a genuine fixed-label cofibration remains a genuine cofibration. -/
theorem map_cofibration {C D : FixedObjects A} (F : C ⟶ D)
    (hF : FixedObjectModel.cofibrations A F) :
    FixedObjectModel.cofibrations O ((functor a).map F) :=
  Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := adjunction a) F hF

/-- The SAME actual original label-pushed object remains cofibrant from genuine original source cofibrancy. -/
theorem object_isCofibrant (C : FixedObjects A) [IsCofibrant C] :
    IsCofibrant ((functor a).obj C) :=
  Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adjunction a) inferInstance

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
