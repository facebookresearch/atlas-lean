/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelPushforwardPresentation

/-! # Whole original interpretations of arbitrary-label pushforward

An actual source enriched functor supplies every original generator map.
Its actual unit and composition laws prove the presentation relations.
The existing full simplicial presentation theorem constructs the whole
extension, retaining all original scalar operators and generator maps.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
open SimplicialQuiver

variable {A O : Type u} (a : A → O) (C : FixedObjects A)
variable {D : FixedObjects O}

/-- Evaluate an original generator through the same source functor and its prescribed image
equalities. -/
def generatorImage (F : C ⟶ LabelRestriction.object a D)
    {x y : O} (q : SimplexCategoryᵒᵖ) (g : Generator a C x y q) :
    (hom D x y).obj q := by
  rcases g with ⟨s, t, hs, ht, c⟩
  cases hs
  cases ht
  exact (homMap F s t).app q c

/-- The whole original generator image is a genuine simplicial map. -/
def imageMap (F : C ⟶ LabelRestriction.object a D) (x y : O) :
    (quiver a C).Hom x y ⟶ hom D x y where
  app q := ↾generatorImage a C F q
  naturality q r f := by
    ext g
    rcases g with ⟨s, t, hs, ht, c⟩
    cases hs
    cases ht
    change (homMap F s t).app r ((hom C s t).map f c) =
      (hom D (a s) (a t)).map f ((homMap F s t).app q c)
    exact ConcreteCategory.congr_hom (C := Type u) ((homMap F s t).naturality f) c

/-- The same whole original Hom map is recovered after its prescribed generator inclusion. -/
theorem inclusion_imageMap (F : C ⟶ LabelRestriction.object a D) (s t : A) :
    inclusion a C s t ≫ imageMap a C F (a s) (a t) = homMap F s t := by
  ext q c
  rfl

/-- The actual target interpretation retains every original target object and generator map. -/
def interpretation (F : C ⟶ LabelRestriction.object a D) : Interpretation (quiver a C) D.val where
  obj := vertex D
  map := imageMap a C F

/-- The entire original length-one Hom path evaluates by the same source functor. -/
theorem source_eval (F : C ⟶ LabelRestriction.object a D) (q : SimplexCategoryᵒᵖ)
    (s t : A) (c : (hom C s t).obj q) :
    (interpretation a C F).evalPath q ((freeSourceHom a C s t).app q c) =
      (homMap F s t).app q c := by
  have h := congrArg (fun m => inclusion a C s t ≫ m)
    ((interpretation a C F).generator_eval (a s) (a t))
  have he := congrArg (fun m => m.app q c) h
  exact he.trans (congrArg (fun m => m.app q c) (inclusion_imageMap a C F s t))

/-- The actual source functor proves every original identity and composition relation. -/
theorem interpretation_relations (F : C ⟶ LabelRestriction.object a D)
    (q : SimplexCategoryᵒᵖ) (x y : O) (p r : Path (quiver a C) q x y)
    (h : relations a C q x y p r) :
    (interpretation a C F).evalPath q p = (interpretation a C F).evalPath q r := by
  cases h with
  | inl h =>
      cases h with
      | mk s =>
          erw [source_eval, Interpretation.evalPath_nil]
          exact congrArg (fun m => m.app q PUnit.unit) (identityMap_homMap F s)
  | inr h =>
      cases h with
      | mk s t r f g =>
          erw [source_eval, Interpretation.evalPath_comp, source_eval, source_eval]
          exact congrArg (fun m => m.app q (f, g)) (compositionMap_homMap F s t r)

/-- The actual relation-respecting original source functor extends to the whole presented target. -/
def desc (F : C ⟶ LabelRestriction.object a D) : object a C ⟶ D :=
  Presentations.extend (quiver a C) (relations a C) D (imageMap a C F)
    (interpretation_relations a C F)

/-- Every entire original target-label generator is read back by the same source functor. -/
theorem generator_desc (F : C ⟶ LabelRestriction.object a D) (x y : O) :
    Presentations.generator (quiver a C) (relations a C) x y ≫
      homMap (desc a C F) x y = imageMap a C F x y :=
  Presentations.generator_extend _ _ _ _ _ x y

/-- Extending the actual source functor and restricting it back recovers every original Hom
and object. -/
theorem unit_desc (F : C ⟶ LabelRestriction.object a D) :
    unit a C ≫ LabelRestriction.map a (desc a C F) = F := by
  apply homMaps_ext
  intro s t
  rw [homMap_comp, homMap_unit, LabelRestriction.homMap_map]
  change (inclusion a C s t ≫ Presentations.generator (quiver a C) (relations a C) (a s) (a t)) ≫
    homMap (desc a C F) (a s) (a t) = homMap F s t
  rw [Category.assoc, generator_desc]
  exact inclusion_imageMap a C F s t

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
