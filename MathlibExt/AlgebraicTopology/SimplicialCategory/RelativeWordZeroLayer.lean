/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeSimplicialWordLayers
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordMaps
import MathlibExt.CategoryTheory.Category.RelativeWordsIsomorphisms

/-!
# The literal original Hom is the zero-word layer

The zero-word comparison retains every actual original Hom simplex and
both individual endpoints. Its two inverse equations follow from the
original word constructors, with no fibrancy or scalar identification
assumption on the starting enrichment.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- Include each same original Hom simplex as its literal zero-letter word. -/
def zeroLayerHom (T : Data C) (a b : O) : hom C a b ⟶ (layer T a b 0).toSSet where
  app q := ↾fun p => ⟨oldWord T q p, Nat.le_refl 0⟩
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    exact (operator_old T f p).symm

/-- The actual zero-word comparison is bijective on every original degree. -/
theorem zeroLayerHom_bijective (T : Data C) (a b : O) (q : SimplexCategoryᵒᵖ) :
    Function.Bijective ((zeroLayerHom T a b).app q) := by
  constructor
  · intro f g h
    exact Word.old.inj (congrArg Subtype.val h)
  · intro p
    obtain ⟨f, hf⟩ := (@length_eq_zero_iff O (scalarCategory C q) (newAt T q) a b p.val).mp
      (Nat.le_zero.mp p.property)
    exact ⟨f, Subtype.ext hf.symm⟩

/-- The same literal zero-word comparison is an actual simplicial isomorphism. -/
instance zeroLayerHom_isIso (T : Data C) (a b : O) : IsIso (zeroLayerHom T a b) := by
  let _ (q : SimplexCategoryᵒᵖ) : IsIso ((zeroLayerHom T a b).app q) :=
    (isIso_iff_bijective _).mpr (zeroLayerHom_bijective T a b q)
  exact NatIso.isIso_of_isIso_app _

/-- Both inverse equations compare the unchanged original Hom and the entire actual zero-word layer. -/
def zeroLayerIso (T : Data C) (a b : O) : hom C a b ≅ (layer T a b 0).toSSet :=
  asIso (zeroLayerHom T a b)

/-- The zero-word comparison followed by the layer inclusion is the same whole original enriched Hom map. -/
theorem zeroLayerHom_ι (T : Data C) (a b : O) : zeroLayerHom T a b ≫ (layer T a b 0).ι = oldHom T a b := rfl

/-- Every original Hom simplex is read back literally by the zero-word inverse. -/
theorem zeroLayerIso_inv_old (T : Data C) (a b : O) (q : SimplexCategoryᵒᵖ) (f : (hom C a b).obj q) :
    (zeroLayerIso T a b).inv.app q ⟨oldWord T q f, Nat.le_refl 0⟩ = f :=
  congr($((zeroLayerIso T a b).hom_inv_id).app q f)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
