/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordEnrichment
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps

/-!
# The actual original and generating maps into the normalized word enrichment

The original enrichment maps by its same literal old Hom words. The
target generators map by actual attaching-domain reduction. The original
quiver square commutes on whole simplicial maps, and the original map
preserves every individual object label, identity and composition.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment

variable {O : Type u} {C : FixedObjects O}

/-- The same original Hom maps into the actual word enrichment as literal old words. -/
def oldHom (T : Data C) (x y : O) : hom C x y ⟶ hom (object T) x y where
  app q := ↾fun p => oldWord T q p
  naturality q r f := by ext p; exact (operator_old T f p).symm

/-- The same original target generator maps by its actual whole attaching-domain reduction. -/
def newHom (T : Data C) (x y : O) : T.target.Hom x y ⟶ hom (object T) x y where
  app q := ↾fun p => letter T q p
  naturality q r f := by ext p; exact (operator_letter T f p).symm

private theorem oldHom_identity (T : Data C) (x : O) :
    identityMap C x ≫ oldHom T x x = identityMap (object T) x := by
  ext q a
  rfl

private theorem oldHom_composition (T : Data C) (x y z : O) :
    compositionMap C x y z ≫ oldHom T x z =
      (oldHom T x y ⊗ₘ oldHom T y z) ≫ compositionMap (object T) x y z := by
  ext q p
  rfl

/-- The actual whole original enriched map, retaining its same individual object labels. -/
def oldMap (T : Data C) : C ⟶ object T :=
  ofHomMaps (oldHom T) (oldHom_identity T) (oldHom_composition T)

/-- The entire actual Hom map of the original enrichment is its same old-word injection. -/
@[simp]
theorem homMap_oldMap (T : Data C) (x y : O) : homMap (oldMap T) x y = oldHom T x y :=
  homMap_ofHomMaps _ _ _ x y

/-- Every original source object maps to the same supplied label of the actual word enrichment. -/
@[simp]
theorem oldMap_obj (T : Data C) (a : C.val) :
    (oldMap T).val.obj a = vertex (object T) (label C a) := rfl

/-- The original attaching quiver square commutes on the same whole original simplicial Hom maps. -/
theorem inclusion_square (T : Data C) (x y : O) :
    T.inclusion x y ≫ newHom T x y = T.attaching x y ≫ oldHom T x y := by
  ext q a
  exact letter_image T q a

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
