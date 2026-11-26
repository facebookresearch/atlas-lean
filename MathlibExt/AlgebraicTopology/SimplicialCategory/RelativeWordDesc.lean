/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordEvaluation

/-!
# The actual enriched extension of a compatible relative attaching cocone

The same whole normalized-word evaluations are simplicial Hom maps and
preserve original identities and compositions. They construct a genuine
fixed-object enriched map whose original and target-generator Hom maps
are read back exactly. No enriched extension outcome is an input.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C D : FixedObjects O}

/-- The entire compatible normalized-word evaluation as a genuine original simplicial Hom map. -/
def descHom (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y)
    (x y : O) : hom (object T) x y ⟶ hom D x y where
  app q := ↾fun p => evalAt T F m q p
  naturality q r f := by ext p; exact (evalAt_operator T F m hm f p).symm

private theorem descHom_identity (T : Data C) (F : C ⟶ D)
    (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y) (x : O) :
    identityMap (object T) x ≫ descHom T F m hm x x = identityMap D x := by
  ext q a
  exact congrArg (fun f => f.app q a) (identityMap_homMap F x)

private theorem descHom_composition (T : Data C) (F : C ⟶ D)
    (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y) (x y z : O) :
    compositionMap (object T) x y z ≫ descHom T F m hm x z =
      (descHom T F m hm x y ⊗ₘ descHom T F m hm y z) ≫ compositionMap D x y z := by
  ext q p
  exact evalAt_comp T F m q p.1 p.2

/-- The actual enriched extension of the supplied compatible original map and target-generator maps. -/
def desc (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y) : object T ⟶ D :=
  ofHomMaps (descHom T F m hm) (descHom_identity T F m hm) (descHom_composition T F m hm)

/-- Its original Hom maps are the same complete normalized-word evaluations. -/
@[simp]
theorem homMap_desc (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y) (x y : O) :
    homMap (desc T F m hm) x y = descHom T F m hm x y := homMap_ofHomMaps _ _ _ x y

/-- The actual extension retains every original individual object label. -/
@[simp]
theorem desc_obj (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y)
    (a : (object T).val) : (desc T F m hm).val.obj a = vertex D (label (object T) a) := rfl

/-- The entire original enrichment factors through its actual normalized-word extension. -/
theorem oldMap_desc (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y) :
    oldMap T ≫ desc T F m hm = F := by
  apply homMaps_ext
  intro x y
  rw [homMap_comp, homMap_oldMap, homMap_desc]
  ext q p
  exact evalAt_old T F m q p

/-- Every original target generator is read back by its same whole supplied simplicial map. -/
theorem newHom_desc (T : Data C) (F : C ⟶ D) (m : ∀ x y : O, T.target.Hom x y ⟶ hom D x y)
    (hm : ∀ x y : O, T.inclusion x y ≫ m x y = T.attaching x y ≫ homMap F x y) (x y : O) :
    newHom T x y ≫ homMap (desc T F m hm) x y = m x y := by
  rw [homMap_desc]
  ext q p
  exact evalAt_letter T F m hm q p

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
