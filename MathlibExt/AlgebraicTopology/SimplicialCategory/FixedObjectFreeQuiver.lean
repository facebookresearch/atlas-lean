/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectHomMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeUniversalProperty

/-!
# The free simplicial quiver in the fixed-object fiber

This is the free enrichment and path-evaluation universal
property, placed in the fixed-object category. Its individual
Objects, generators and enriched maps are unchanged. Component
quiver maps extend by the free universal property.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiver
open SimplicialQuiver

variable {O : Type u}

/-- The free simplicial enrichment on the specified Hom family, with object set `O`. -/
abbrev object (Q : Data O) : FixedObjects O := ⟨free Q, rfl⟩

/-- The inclusion of generating Hom simplices as one-edge paths. -/
abbrev generator (Q : Data O) (x y : O) : Q.Hom x y ⟶ hom (object Q) x y :=
  SimplicialQuiver.generator Q x y

/-- Extend maps on generating Hom objects to a functor from the free enrichment. -/
def extend (Q : Data O) (D : FixedObjects O) (m : ∀ x y : O, Q.Hom x y ⟶ hom D x y) :
    object Q ⟶ D := by
  let I : Interpretation Q D.val := ⟨vertex D, m⟩
  let F : (object Q).val ⟶ D.val := I.extend
  refine ⟨F, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) F rfl D.property
  ext x
  rfl

/-- Every generator is read back by its same supplied simplicial map. -/
theorem generator_extend (Q : Data O) (D : FixedObjects O)
    (m : ∀ x y : O, Q.Hom x y ⟶ hom D x y) (x y : O) :
    generator Q x y ≫ homMap (extend Q D m) x y = m x y := by
  let I : Interpretation Q D.val := ⟨vertex D, m⟩
  change SimplicialQuiver.generator Q x y ≫ (I.evalHom x y ≫ 𝟙 (hom D x y)) = m x y
  rw [Category.comp_id]
  exact I.generator_eval x y

set_option backward.isDefEq.respectTransparency.types false in
/-- Free enriched maps are determined by their same generators. -/
theorem generators_ext (Q : Data O) {D : FixedObjects O} {F G : object Q ⟶ D}
    (h : ∀ x y : O, generator Q x y ≫ homMap F x y = generator Q x y ≫ homMap G x y) :
    F = G := by
  rcases F with ⟨F, hF⟩
  rcases G with ⟨G, hG⟩
  rcases F with ⟨objF, mapF, idF, compF⟩
  rcases G with ⟨objG, mapG, idG, compG⟩
  have hoF : objF = vertex D := funext fun a =>
    map_vertex (C := object Q) (D := D) ⟨⟨objF, mapF, idF, compF⟩, hF⟩ a
  have hoG : objG = vertex D := funext fun a =>
    map_vertex (C := object Q) (D := D) ⟨⟨objG, mapG, idG, compG⟩, hG⟩ a
  subst objF
  subst objG
  apply Functor.Fiber.hom_ext
  apply (interpretationEquiv Q).injective
  change Interpretation.mk (vertex D) (fun x y => SimplicialQuiver.generator Q x y ≫ mapF x y) =
    Interpretation.mk (vertex D) (fun x y => SimplicialQuiver.generator Q x y ≫ mapG x y)
  apply congrArg (Interpretation.mk (vertex D))
  funext x y
  have hh := h x y
  change SimplicialQuiver.generator Q x y ≫ (mapF x y ≫ 𝟙 (hom D x y)) =
    SimplicialQuiver.generator Q x y ≫ (mapG x y ≫ 𝟙 (hom D x y)) at hh
  simpa only [Category.comp_id] using hh

/-- Extend the same componentwise simplicial-quiver map. -/
def map {Q R : Data O} (i : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y) : object Q ⟶ object R :=
  extend Q (object R) (fun x y => i x y ≫ generator R x y)

/-- Every source generator maps to its same target generator after the supplied
quiver map. -/
theorem generator_map {Q R : Data O} (i : ∀ x y : O, Q.Hom x y ⟶ R.Hom x y) (x y : O) :
    generator Q x y ≫ homMap (map i) x y = i x y ≫ generator R x y :=
  generator_extend Q (object R) _ x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeQuiver
