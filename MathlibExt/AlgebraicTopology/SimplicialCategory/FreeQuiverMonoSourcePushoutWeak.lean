/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourcePushout
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeQuiverMonoPushoutScalarPresentation

/-!
# Genuine weak cobase change along every actual monic free-quiver pushout

The complete supplied pushout of an original monic free-quiver map is
compared with the SAME relative word object by the existing canonical
comparison. Its full old Hom map is monic. A second actual pushout of
any honest Homwise weak source map is weak on its SAME original map,
by the proved original source-word comparison. All full maps and object
labels remain those of the two supplied original squares.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
variable {O : Type u} {C : FixedObjects O}

/-- Every original Hom simplex includes injectively as its SAME whole zero-letter word. -/
theorem homMap_oldMap_mono (T : Data C) (a b : O) : Mono (homMap (oldMap T) a b) := by
  rw [homMap_oldMap, NatTrans.mono_iff_mono_app]
  intro q
  apply (mono_iff_injective _).mpr
  intro h k he
  exact RelativeWords.Word.old.inj he

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiverMonoPushout
open RelativeAttachment
variable {O : Type u} {Q R : SimplicialQuiver.Data O} {C P D E : FixedObjects O}
  (m : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y)
  (hm : ∀ x y, Mono (m x y)) (s : FreeQuiver.object Q ⟶ C)
  (j : C ⟶ P) (k : FreeQuiver.object R ⟶ P)
  (hp : IsPushout s (FreeQuiver.map m) j k)

include hm hp in
/-- Every SAME complete old Hom map in any actual mono-quiver pushout is monic. -/
theorem leftHom_mono (a b : O) : Mono (homMap j a b) := by
  let e := comparison m hm s j k hp
  have he : homMap (oldMap (data m hm s)) a b ≫ homMap e.hom a b = homMap j a b :=
    (homMap_comp _ _ a b).symm.trans
      (congrArg (fun f => homMap f a b) (oldMap_comparison m hm s j k hp))
  let _ : Mono (homMap (oldMap (data m hm s)) a b) := homMap_oldMap_mono _ a b
  let _ : IsIso (homMap e.hom a b) := inferInstanceAs (IsIso ((evaluation a b).map e.hom))
  rw [← he]
  infer_instance

include hm hp in
/-- The SAME weak source map remains weak after actual cobase change along this original mono-quiver pushout. -/
theorem sourcePushout_weak (F : C ⟶ D) (hF : FixedObjectModel.weakEquivalences O F)
    (d : P ⟶ E) (c : D ⟶ E) (sq : IsPushout j F d c) :
    FixedObjectModel.weakEquivalences O d := by
  let e := comparison m hm s j k hp
  have he : oldMap (data m hm s) ≫ e.hom = j := oldMap_comparison m hm s j k hp
  have hsq : IsPushout (oldMap (data m hm s)) F (e.hom ≫ d) c :=
    sq.of_iso' (Iso.refl _) e (Iso.refl _) (Iso.refl _)
      (by simpa only [Iso.refl_hom, Category.id_comp] using he.symm) (by simp) (by simp) (by simp)
  have h := sourceChange_pushout_weak (data m hm s) F hF (e.hom ≫ d) c hsq
  exact ((FixedObjectModel.weakEquivalences O).cancel_left_of_respectsIso e.hom d).mp h

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiverMonoPushout
