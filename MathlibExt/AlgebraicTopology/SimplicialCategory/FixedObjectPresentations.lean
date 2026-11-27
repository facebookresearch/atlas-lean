/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.PresentationUniversalProperty

/-!
# Actual presentations in the fixed-object enriched category

The existing simplicial presentation is placed in the actual object
fiber. Relation-respecting original generator maps construct a genuine
fixed-object map. Whole maps are determined by those generators, using
the already proved full presentation universal property.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.Presentations
open SimplicialQuiver

variable {O : Type u} (Q : Data O) (R : Relations Q)

/-- The actual presented enrichment with the unchanged original object labels. -/
abbrev object : FixedObjects O := ⟨presented R, rfl⟩

/-- The whole original generating Hom map into the actual presented enrichment. -/
def generator (x y : O) : Q.Hom x y ⟶ hom (object Q R) x y :=
  SimplicialQuiver.generator Q x y ≫ quotientHom R x y

/-- Every actual stated relation gives the same original presented Hom simplex. -/
theorem relation_eq (q : SimplexCategoryᵒᵖ) (x y : O) (p r : Path Q q x y)
    (h : R q x y p r) :
    (quotientHom R x y).app q p = (quotientHom R x y).app q r :=
  _root_.Quotient.sound (Closure.relation h)

/-- Extend actual original generators whose evaluations prove every stated relation. -/
def extend (D : FixedObjects O) (m : ∀ x y : O, Q.Hom x y ⟶ hom D x y)
    (hR : ∀ q x y p r, R q x y p r →
      (Interpretation.mk (vertex D) m).evalPath q p =
        (Interpretation.mk (vertex D) m).evalPath q r) : object Q R ⟶ D := by
  let I : Interpretation Q D.val := ⟨vertex D, m⟩
  let F : (object Q R).val ⟶ D.val := I.descend R hR
  refine ⟨F, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) F rfl D.property
  ext a
  rfl

/-- The constructed map retains the same individual original object label. -/
@[simp]
theorem extend_obj (D : FixedObjects O) (m : ∀ x y : O, Q.Hom x y ⟶ hom D x y)
    (hR : ∀ q x y p r, R q x y p r →
      (Interpretation.mk (vertex D) m).evalPath q p =
        (Interpretation.mk (vertex D) m).evalPath q r) (a : O) :
    (extend Q R D m hR).val.obj a = vertex D a := rfl

/-- Every original generator is read back by its same whole supplied simplicial map. -/
@[simp]
theorem generator_extend (D : FixedObjects O) (m : ∀ x y : O, Q.Hom x y ⟶ hom D x y)
    (hR : ∀ q x y p r, R q x y p r →
      (Interpretation.mk (vertex D) m).evalPath q p =
        (Interpretation.mk (vertex D) m).evalPath q r) (x y : O) :
    generator Q R x y ≫ homMap (extend Q R D m hR) x y = m x y := by
  let I : Interpretation Q D.val := ⟨vertex D, m⟩
  change (SimplicialQuiver.generator Q x y ≫ quotientHom R x y) ≫
    (I.descendHom R hR x y ≫ 𝟙 (hom D x y)) = m x y
  rw [Category.comp_id, Category.assoc, I.quotient_descend]
  exact I.generator_eval x y

/-- Whole original fixed-object presentation maps are determined by their actual generators. -/
theorem generators_ext {D : FixedObjects O} {F G : object Q R ⟶ D}
    (h : ∀ x y : O, generator Q R x y ≫ homMap F x y = generator Q R x y ≫ homMap G x y) :
    F = G := by
  rcases F with ⟨F, hF⟩
  rcases G with ⟨G, hG⟩
  rcases F with ⟨objF, mapF, idF, compF⟩
  rcases G with ⟨objG, mapG, idG, compG⟩
  have hoF : objF = vertex D := funext fun a =>
    map_vertex (C := object Q R) (D := D) ⟨⟨objF, mapF, idF, compF⟩, hF⟩ a
  have hoG : objG = vertex D := funext fun a =>
    map_vertex (C := object Q R) (D := D) ⟨⟨objG, mapG, idG, compG⟩, hG⟩ a
  subst objF
  subst objG
  apply Functor.Fiber.hom_ext
  apply (presentedInterpretationEquiv R).injective
  apply Subtype.ext
  change Interpretation.mk (vertex D)
      (fun x y => SimplicialQuiver.generator Q x y ≫ quotientHom R x y ≫ mapF x y) =
    Interpretation.mk (vertex D)
      (fun x y => SimplicialQuiver.generator Q x y ≫ quotientHom R x y ≫ mapG x y)
  apply congrArg (Interpretation.mk (vertex D))
  funext x y
  have hh := h x y
  change (SimplicialQuiver.generator Q x y ≫ quotientHom R x y) ≫
      (mapF x y ≫ 𝟙 (hom D x y)) =
    (SimplicialQuiver.generator Q x y ≫ quotientHom R x y) ≫
      (mapG x y ≫ 𝟙 (hom D x y)) at hh
  have hpF := (congrArg (fun k =>
    (SimplicialQuiver.generator Q x y ≫ quotientHom R x y) ≫ k) (Category.comp_id (mapF x y))).trans
      (Category.assoc _ _ _)
  have hpG := (congrArg (fun k =>
    (SimplicialQuiver.generator Q x y ≫ quotientHom R x y) ≫ k) (Category.comp_id (mapG x y))).trans
      (Category.assoc _ _ _)
  exact hpF.symm.trans (hh.trans hpG)

end CategoryTheory.SimplicialEnrichment.FixedObjects.Presentations
