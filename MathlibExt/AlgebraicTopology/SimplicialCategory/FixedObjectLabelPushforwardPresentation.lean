/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectLabelRestriction
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectPresentations

/-! # Original path presentation for arbitrary-label enriched pushforward

Each generator retains its original source label, target label and whole
Hom simplex, together with the prescribed two image equalities. Free
paths use the target labels. Only original identity and original
composition equations generate the simplicial congruence; distinct
source objects with equal images are not treated as the same source.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
open SimplicialQuiver

variable {A O : Type u} (a : A → O) (C : FixedObjects A)

/-- An original Hom generator retains both original labels and both prescribed target images. -/
structure Generator (x y : O) (q : SimplexCategoryᵒᵖ) where
  /-- Its original source object. -/
  source : A
  /-- Its original target object. -/
  target : A
  /-- Its original source has the specified target label. -/
  source_eq : a source = x
  /-- Its original target has the specified target label. -/
  target_eq : a target = y
  /-- The entire original Hom simplex in the same scalar degree. -/
  simplex : (hom C source target).obj q

/-- All original Hom generators at two target labels, with every original scalar operator. -/
def generatedHom (x y : O) : SSet.{u} where
  obj q := Generator a C x y q
  map f := ↾fun g => ⟨g.source, g.target, g.source_eq, g.target_eq,
    (hom C g.source g.target).map f g.simplex⟩
  map_id q := by
    ext g
    rcases g with ⟨s, t, hs, ht, c⟩
    change Generator.mk s t hs ht ((hom C s t).map (𝟙 q) c) = Generator.mk s t hs ht c
    rw [(hom C s t).map_id]
    rfl
  map_comp f g := by
    ext c
    rcases c with ⟨s, t, hs, ht, c⟩
    change Generator.mk s t hs ht ((hom C s t).map (f ≫ g) c) =
      Generator.mk s t hs ht ((hom C s t).map g ((hom C s t).map f c))
    rw [(hom C s t).map_comp]
    rfl

/-- The actual generating quiver on all prescribed target labels. -/
def quiver : Data O := ⟨generatedHom a C⟩

/-- A whole original Hom maps to its same generator at its two prescribed target labels. -/
def inclusion (s t : A) : hom C s t ⟶ (quiver a C).Hom (a s) (a t) where
  app q := ↾fun c => ⟨s, t, rfl, rfl, c⟩
  naturality q r f := by ext c; rfl

/-- Each original Hom simplex gives its actual length-one path on the target labels. -/
def freeSourceHom (s t : A) : hom C s t ⟶ freeHom (quiver a C) (a s) (a t) :=
  inclusion a C s t ≫ SimplicialQuiver.generator (quiver a C) (a s) (a t)

/-- Each original identity is identified with the empty path at its same target image. -/
inductive UnitRelation : ∀ (q : SimplexCategoryᵒᵖ) (x y : O),
    Path (quiver a C) q x y → Path (quiver a C) q x y → Prop where
  | mk (q : SimplexCategoryᵒᵖ) (s : A) :
      UnitRelation q (a s) (a s)
        ((freeSourceHom a C s s).app q ((identityMap C s).app q PUnit.unit))
        (@Quiver.Path.nil O (quiverAt (quiver a C) q) (a s))

/-- Each original composable pair is identified with its actual original composite. -/
inductive CompositionRelation : ∀ (q : SimplexCategoryᵒᵖ) (x y : O),
    Path (quiver a C) q x y → Path (quiver a C) q x y → Prop where
  | mk (q : SimplexCategoryᵒᵖ) (s t r : A)
      (f : (hom C s t).obj q) (g : (hom C t r).obj q) :
      CompositionRelation q (a s) (a r)
        ((freeSourceHom a C s r).app q ((compositionMap C s t r).app q (f, g)))
        (@Quiver.Path.comp O (quiverAt (quiver a C) q) (a s) (a t) (a r)
          ((freeSourceHom a C s t).app q f) ((freeSourceHom a C t r).app q g))

/-- Only the supplied original identity and composition families generate the canonical
congruence. -/
def relations : Relations (quiver a C) := fun q x y p r =>
  UnitRelation a C q x y p r ∨ CompositionRelation a C q x y p r

/-- The actual quotient of original free paths, keeping every prescribed target label. -/
abbrev object : FixedObjects O := Presentations.object (quiver a C) (relations a C)

/-- The whole original source Hom map into the actual presented target. -/
def unitHom (s t : A) : hom C s t ⟶ hom (object a C) (a s) (a t) :=
  inclusion a C s t ≫ Presentations.generator (quiver a C) (relations a C) (a s) (a t)

private theorem unitHom_identity (s : A) :
    identityMap C s ≫ unitHom a C s s = identityMap (object a C) (a s) := by
  ext q c
  cases c
  exact Presentations.relation_eq (quiver a C) (relations a C) q (a s) (a s) _ _
    (Or.inl (UnitRelation.mk (a := a) (C := C) q s))

private theorem unitHom_composition (s t r : A) :
    compositionMap C s t r ≫ unitHom a C s r =
      (unitHom a C s t ⊗ₘ unitHom a C t r) ≫
        compositionMap (object a C) (a s) (a t) (a r) := by
  ext q c
  rcases c with ⟨f, g⟩
  exact Presentations.relation_eq (quiver a C) (relations a C) q (a s) (a r) _ _
    (Or.inr (CompositionRelation.mk (a := a) (C := C) q s t r f g))

/-- The actual source map into the restricted presented target preserves the full original
enriched laws. -/
def unit : C ⟶ LabelRestriction.object a (object a C) :=
  ofHomMaps (unitHom a C) (unitHom_identity a C) (unitHom_composition a C)

/-- Every original source Hom is read back as the identical whole generator inclusion. -/
@[simp]
theorem homMap_unit (s t : A) : homMap (unit a C) s t = unitHom a C s t :=
  homMap_ofHomMaps _ _ _ s t

end CategoryTheory.SimplicialEnrichment.FixedObjects.LabelPushforward
