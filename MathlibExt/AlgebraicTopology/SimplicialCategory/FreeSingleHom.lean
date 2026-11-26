/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjects
import MathlibExt.AlgebraicTopology.SimplicialCategory.SingleHomQuiver

/-!
# The free singleHom object in the fixed-object fiber

Restriction and path extension are inverse on enriched functors
that fix every object label. Their target object map is the
literal equality transport furnished by the functor fiber.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom
open SimplicialQuiver

variable {O : Type u} (x y : O)

/-- The free enrichment, with the fixed object labels. -/
abbrev object (X : SSet.{u}) : FixedObjects O :=
  ⟨SimplicialQuiver.free (SingleHom.quiver x y X), rfl⟩

/-- Every free vertex has exactly its supplied fixed label. -/
@[simp]
theorem vertex_object (X : SSet.{u}) (a : O) :
    vertex (object x y X) a = a := rfl

/-- The specified generator, as a map into the free Hom. -/
def generator (X : SSet.{u}) : X ⟶ hom (object x y X) x y :=
  eqToHom (SingleHom.quiver_at x y X).symm ≫
    SimplicialQuiver.generator (SingleHom.quiver x y X) x y

/-- Restrict a fixed-object enriched map to the supplied generator. -/
def restrict (X : SSet.{u}) (D : FixedObjects O) (F : object x y X ⟶ D) :
    X ⟶ hom D x y := generator x y X ≫ homMap F x y

/-- Extend the supplied Hom map by evaluation of every free path. -/
def extend (X : SSet.{u}) (D : FixedObjects O) (f : X ⟶ hom D x y) :
    object x y X ⟶ D := by
  let I := SingleHom.interpretation x y X (vertex D) f
  let F : (object x y X).val ⟶ D.val := I.extend
  refine ⟨F, ?_⟩
  apply IsHomLift.of_fac' forgetObjects (𝟙 O) F rfl D.property
  ext a
  rfl

/-- The extension fixes the label at every object. -/
@[simp]
theorem extend_obj (X : SSet.{u}) (D : FixedObjects O) (f : X ⟶ hom D x y) (a : O) :
    (extend x y X D f).val.obj a = vertex D a := rfl

/-- Restriction of the path extension recovers the same simplicial Hom map. -/
@[simp]
theorem restrict_extend (X : SSet.{u}) (D : FixedObjects O) (f : X ⟶ hom D x y) :
    restrict x y X D (extend x y X D f) = f := by
  change (eqToHom (SingleHom.quiver_at x y X).symm ≫
    SimplicialQuiver.generator (SingleHom.quiver x y X) x y) ≫
      ((SingleHom.interpretation x y X (vertex D) f).evalHom x y ≫ 𝟙 (hom D x y)) = f
  simpa only [SingleHom.interpretation, Category.comp_id, Category.assoc] using
    SingleHom.generator_extend x y X (vertex D) f

/-- The enriched functor is recovered, including all finite path simplices. -/
@[simp]
theorem extend_restrict (X : SSet.{u}) (D : FixedObjects O) (F : object x y X ⟶ D) :
    extend x y X D (restrict x y X D F) = F := by
  rcases F with ⟨F, hF⟩
  rcases F with ⟨obj, map, hi, hc⟩
  have ho : obj = vertex D := by
    funext a
    exact map_vertex (C := object x y X) (D := D) ⟨⟨obj, map, hi, hc⟩, hF⟩ a
  subst obj
  apply Functor.Fiber.hom_ext
  let Q := SingleHom.quiver x y X
  let G : EnrichedFunctor SSet.{u} (SimplicialQuiver.free Q) D.val :=
    ⟨vertex D, map, hi, hc⟩
  have hs : restrict x y X D ⟨G, hF⟩ =
      SingleHom.restrict x y X (vertex D)
        (fun a b => SimplicialQuiver.generator Q a b ≫ map a b) := by
    change (eqToHom _ ≫ SimplicialQuiver.generator Q x y) ≫
      (map x y ≫ 𝟙 (hom D x y)) =
      eqToHom _ ≫ (SimplicialQuiver.generator Q x y ≫ map x y)
    exact (congrArg (fun k =>
      (eqToHom (SingleHom.quiver_at x y X).symm ≫ SimplicialQuiver.generator Q x y) ≫ k)
      (Category.comp_id (map x y))).trans (Category.assoc _ _ _)
  have he : SingleHom.interpretation x y X (vertex D)
      (restrict x y X D ⟨G, hF⟩) = SimplicialQuiver.restrict Q G := by
    rw [hs]
    exact congrArg (Interpretation.mk (vertex D))
      (SingleHom.maps_restrict x y X (vertex D)
        (fun a b => SimplicialQuiver.generator Q a b ≫ map a b))
  change (SingleHom.interpretation x y X (vertex D)
    (restrict x y X D ⟨G, hF⟩)).extend = G
  rw [he]
  exact SimplicialQuiver.extend_restrict Q G

/-- Maps from the free singleHom enrichment correspond to maps into the selected Hom object. -/
def homEquiv (X : SSet.{u}) (D : FixedObjects O) :
    (object x y X ⟶ D) ≃ (X ⟶ hom D x y) where
  toFun := restrict x y X D
  invFun := extend x y X D
  left_inv := extend_restrict x y X D
  right_inv := restrict_extend x y X D

/-- Restriction commutes with the same target enriched map. -/
theorem restrict_comp (X : SSet.{u}) {C D : FixedObjects O}
    (F : object x y X ⟶ C) (G : C ⟶ D) :
    restrict x y X D (F ≫ G) = restrict x y X C F ≫ homMap G x y := by
  simp only [restrict, homMap_comp, Category.assoc]

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom
