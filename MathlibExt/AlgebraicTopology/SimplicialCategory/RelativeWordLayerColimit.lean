/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeSimplicialWordLayers
import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape

/-!
# The actual colimit of all original word-length layers

Every original normalized word occurs in the layer of its literal finite
length. Cocone evaluation at that same word proves the entire simplicial
colimit universal property. Simplicial operators may lower length; the
actual cocone relation identifies the lower and higher stage evaluations.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- Literal normalized word length in the same original scalar degree. -/
abbrev wordLength (T : Data C) (q : SimplexCategoryᵒᵖ) {a b : O} (p : WordAt T q a b) : ℕ :=
  @Word.length O (scalarCategory C q) (newAt T q) a b p

/-- The actual increasing sequence of all original normalized word-length layers. -/
def wordLayerDiagram (T : Data C) (a b : O) : ℕ ⥤ SSet.{u} where
  obj n := (layer T a b n).toSSet
  map f := Subfunctor.homOfLe (fun _ _ hp => hp.trans (leOfHom f))
  map_id _n := rfl
  map_comp _f _g := rfl

/-- Every sequence step is the same actual original word-layer inclusion. -/
theorem wordLayerDiagram_step (T : Data C) (a b : O) (n : ℕ) :
    (wordLayerDiagram T a b).map (homOfLE (Nat.le_succ n)) = layerInclusion T a b n := rfl

/-- The same original words include every finite layer in the entire normalized Hom object. -/
def wordLayerCocone (T : Data C) (a b : O) : Cocone (wordLayerDiagram T a b) where
  pt := wordHom T a b
  ι := { app n := (layer T a b n).ι, naturality _n _m _f := rfl }

/-- Evaluate a supplied layer cocone at the same original word in the indicated actual layer. -/
def wordLayerValue (T : Data C) (a b : O) (s : Cocone (wordLayerDiagram T a b))
    (q : SimplexCategoryᵒᵖ) (p : WordAt T q a b) (n : ℕ) (hp : wordLength T q p ≤ n) : s.pt.obj q :=
  (s.ι.app n).app q ⟨p, hp⟩

/-- Every larger layer evaluation equals evaluation at the literal original word length. -/
theorem wordLayerValue_minimal (T : Data C) (a b : O) (s : Cocone (wordLayerDiagram T a b))
    (q : SimplexCategoryᵒᵖ) (p : WordAt T q a b) (n : ℕ) (hp : wordLength T q p ≤ n) :
    wordLayerValue T a b s q p n hp =
      wordLayerValue T a b s q p (wordLength T q p) (Nat.le_refl _) :=
  congr($(s.w (homOfLE hp)).app q ⟨p, Nat.le_refl _⟩)

/-- The actual whole simplicial map from the word-layer cocone evaluates each original finite word. -/
def wordLayerDesc (T : Data C) (a b : O) (s : Cocone (wordLayerDiagram T a b)) : wordHom T a b ⟶ s.pt where
  app q := ↾fun p => wordLayerValue T a b s q p (wordLength T q p) (Nat.le_refl _)
  naturality q r f := by
    apply ConcreteCategory.hom_ext
    intro p
    let p' := operator T f p
    have hp : wordLength T r p' ≤ wordLength T q p := operator_length_le T f p
    calc
      wordLayerValue T a b s r p' (wordLength T r p') (Nat.le_refl _) =
        wordLayerValue T a b s r p' (wordLength T q p) hp :=
          (wordLayerValue_minimal T a b s r p' (wordLength T q p) hp).symm
      _ = s.pt.map f (wordLayerValue T a b s q p (wordLength T q p) (Nat.le_refl _)) :=
        congr($((s.ι.app (wordLength T q p)).naturality f) ⟨p, Nat.le_refl _⟩)

/-- The entire original normalized Hom is the genuine colimit of its actual finite word layers. -/
def wordLayerIsColimit (T : Data C) (a b : O) : IsColimit (wordLayerCocone T a b) where
  desc := wordLayerDesc T a b
  fac s n := by
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    exact (wordLayerValue_minimal T a b s q p.val n p.property).symm
  uniq s m h := by
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    exact congr($(h (wordLength T q p)).app q ⟨p, Nat.le_refl _⟩)

/-- The zero-word layer inclusion is the actual countable transfinite composite of all finite layer steps. -/
def zeroLayerComposition (T : Data C) (a b : O) :
    CategoryTheory.TransfiniteCompositionOfShape ℕ (layer T a b 0).ι where
  F := wordLayerDiagram T a b
  isoBot := Iso.refl _
  incl := (wordLayerCocone T a b).ι
  isColimit := wordLayerIsColimit T a b
  fac := Category.id_comp _

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
