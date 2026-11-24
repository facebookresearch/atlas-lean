/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeSingleHom
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual fixed-object free single-Hom adjunction

The left adjoint freely inserts the supplied Hom generators among the
original object labels. Its right adjoint evaluates the original Hom.
Both triangles are equalities of the actual whole maps, including every
free path simplex.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom

variable {O : Type u} (x y : O)

/-- Apply the supplied scalar map on the original generator and extend on all free paths. -/
def map {X Y : SSet.{u}} (f : X ⟶ Y) : object x y X ⟶ object x y Y :=
  extend x y X (object x y Y) (f ≫ generator x y Y)

/-- The whole generator square of the same actual free map. -/
@[simp]
theorem generator_map {X Y : SSet.{u}} (f : X ⟶ Y) :
    generator x y X ≫ homMap (map x y f) x y = f ≫ generator x y Y :=
  restrict_extend x y X (object x y Y) (f ≫ generator x y Y)

/-- Restriction of a free-map composite is the original scalar precomposition. -/
theorem restrict_map_comp {X Y : SSet.{u}} (f : X ⟶ Y) (D : FixedObjects O)
    (F : object x y Y ⟶ D) :
    restrict x y X D (map x y f ≫ F) = f ≫ restrict x y Y D F := by
  rw [restrict_comp]
  change (generator x y X ≫ homMap (map x y f) x y) ≫ homMap F x y =
    f ≫ (generator x y Y ≫ homMap F x y)
  rw [generator_map, Category.assoc]

/-- The free map of the scalar identity is the whole enriched identity. -/
@[simp]
theorem map_id (X : SSet.{u}) : map x y (𝟙 X) = 𝟙 (object x y X) := by
  apply (homEquiv x y X (object x y X)).injective
  change restrict x y X (object x y X) (map x y (𝟙 X)) =
    restrict x y X (object x y X) (𝟙 _)
  rw [map, restrict_extend]
  simp only [restrict, homMap_id, Category.id_comp, Category.comp_id]

/-- Composition retains the actual original generator maps and all their finite words. -/
@[simp]
theorem map_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map x y (f ≫ g) = map x y f ≫ map x y g := by
  apply (homEquiv x y X (object x y Z)).injective
  change restrict x y X (object x y Z) (map x y (f ≫ g)) =
    restrict x y X (object x y Z) (map x y f ≫ map x y g)
  rw [restrict_map_comp]
  simp only [map, restrict_extend, Category.assoc]

/-- The actual free single-Hom functor into the existing fixed-object category. -/
def functor : SSet.{u} ⥤ FixedObjects O where
  obj := object x y
  map := map x y
  map_id := map_id x y
  map_comp := map_comp x y

/-- Actual source naturality of extension, proved on the entire original enriched maps. -/
theorem extend_precompose {X Y : SSet.{u}} (f : X ⟶ Y) (D : FixedObjects O)
    (g : Y ⟶ hom D x y) :
    extend x y X D (f ≫ g) = map x y f ≫ extend x y Y D g := by
  apply (homEquiv x y X D).injective
  change restrict x y X D (extend x y X D (f ≫ g)) =
    restrict x y X D (map x y f ≫ extend x y Y D g)
  rw [restrict_extend, restrict_map_comp, restrict_extend]

/-- The genuine adjunction, obtained from the proved original restriction/extension equivalence. -/
def adjunction : functor x y ⊣ evaluation x y :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv x y
    homEquiv_naturality_left_symm := fun f g => extend_precompose x y f _ g
    homEquiv_naturality_right := fun F G => restrict_comp x y _ F G }

/-- The actual adjunction unit is the original length-one generator map. -/
theorem unit_app (X : SSet.{u}) :
    (adjunction x y).unit.app X = generator x y X := by
  change generator x y X ≫ homMap (𝟙 (object x y X)) x y = generator x y X
  rw [homMap_id, Category.comp_id]

/-- The actual counit evaluates every free word in the original target enriched category. -/
theorem counit_app (D : FixedObjects O) :
    (adjunction x y).counit.app D = extend x y (hom D x y) D (𝟙 _) := rfl

/-- The entire free enriched map satisfies the left triangle, not merely its generating vertices. -/
theorem free_triangle (X : SSet.{u}) :
    (functor x y).map (generator x y X) ≫
      (adjunction x y).counit.app (object x y X) = 𝟙 (object x y X) := by
  have h := (adjunction x y).left_triangle_components X
  change map x y ((adjunction x y).unit.app X) ≫
    (adjunction x y).counit.app (object x y X) = 𝟙 (object x y X) at h
  rw [unit_app] at h
  exact h

/-- The entire evaluated Hom map satisfies the right triangle on every original simplex. -/
theorem hom_triangle (D : FixedObjects O) :
    generator x y (hom D x y) ≫
      homMap ((adjunction x y).counit.app D) x y = 𝟙 (hom D x y) := by
  have h := (adjunction x y).right_triangle_components D
  change (adjunction x y).unit.app (hom D x y) ≫
    homMap ((adjunction x y).counit.app D) x y = 𝟙 (hom D x y) at h
  rw [unit_app] at h
  exact h

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeSingleHom
