/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Reedy.SimplexCategory
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import MathlibExt.CategoryTheory.Reedy.FiniteBoundaries

/-!
# The original simplex category and its opposite are Reedy

The degree is the original simplex length. The direct maps are exactly the
original monomorphisms and the inverse maps are exactly the original
epimorphisms. The complete factor record is the original epi--image--mono
factorization; uniqueness retains that middle simplex and both maps.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Simplicial

namespace SimplexCategory

/-- The complete original epi--image--mono factorization of a simplex map. -/
def reedyFactor {i j : SimplexCategory} (f : i ⟶ j) :
    ReedyFactorization (monomorphisms SimplexCategory) (epimorphisms SimplexCategory) f :=
  MorphismProperty.MapFactorizationData.mk (image f) (factorThruImage f) (image.ι f)
    (image.fac f) inferInstance inferInstance

/-- Every original complete epi--mono factor is the canonical native record. -/
theorem reedyFactor_unique {i j : SimplexCategory} (f : i ⟶ j)
    (a : ReedyFactorization (monomorphisms SimplexCategory) (epimorphisms SimplexCategory) f) :
    a = reedyFactor f := by
  let := reedyStructure.subsingleton_mapFactorizationData f
  exact Subsingleton.elim _ _

/-- The original image factor is exactly Mathlib's selected native factor, including both maps. -/
theorem reedyFactor_eq_canonical {i j : SimplexCategory} (f : i ⟶ j) :
    reedyFactor f = reedyStructure.mapFactorizationData f :=
  (reedyFactor_unique f _).symm

/-- The ordinary simplex Reedy interface uses the established canonical Reedy structure. -/
def reedy : CategoryTheory.ReedyStructure SimplexCategory ℕ :=
  { CategoryTheory.ReedyStructure.ofCanonical reedyStructure with factor := reedyFactor }

/-- The actual opposite simplex category's ordinary Reedy structure. -/
def reedyOp : CategoryTheory.ReedyStructure SimplexCategoryᵒᵖ ℕ := reedy.op

/-- The original simplex length is the actual Reedy degree. -/
@[simp]
theorem reedy_degree (i : SimplexCategory) : reedy.degree i = i.len := rfl

/-- Original simplex monomorphisms are exactly the direct maps. -/
@[simp]
theorem reedy_direct {i j : SimplexCategory} (f : i ⟶ j) : reedy.direct f ↔ Mono f := Iff.rfl

/-- Original simplex epimorphisms are exactly the inverse maps. -/
@[simp]
theorem reedy_inverse {i j : SimplexCategory} (f : i ⟶ j) : reedy.inverse f ↔ Epi f := Iff.rfl

/-- The actual Reedy middle simplex is the original image simplex. -/
@[simp]
theorem reedy_factor_middle {i j : SimplexCategory} (f : i ⟶ j) :
    (reedy.factor f).middle = image f := rfl

/-- The actual Reedy inverse arrow is the original image factor. -/
@[simp]
theorem reedy_factor_inverseMap {i j : SimplexCategory} (f : i ⟶ j) :
    (reedy.factor f).inverseMap = factorThruImage f := rfl

/-- The actual Reedy direct arrow is the original image inclusion. -/
@[simp]
theorem reedy_factor_directMap {i j : SimplexCategory} (f : i ⟶ j) :
    (reedy.factor f).directMap = image.ι f := rfl

/-- The actual opposite simplex degree is its original underlying length. -/
@[simp]
theorem reedyOp_degree (i : SimplexCategoryᵒᵖ) : reedyOp.degree i = i.unop.len := rfl

/-- Opposite direct maps are exactly the original underlying epimorphisms. -/
@[simp]
theorem reedyOp_direct {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    reedyOp.direct f ↔ Epi f.unop := Iff.rfl

/-- Opposite inverse maps are exactly the original underlying monomorphisms. -/
@[simp]
theorem reedyOp_inverse {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j) :
    reedyOp.inverse f ↔ Mono f.unop := Iff.rfl

end SimplexCategory

end
end
end

section



/-!
# Actual finite simplex latching and matching boundaries

Both the original simplex category and its opposite have finite original
degree downsets and finite original Hom types. All four actual boundary
categories are finite. Their actual (co)limit cones and boundary maps
therefore require only finite limits and colimits of the coefficient
category. Every original simplex comparison and coefficient map is retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uC vC

open CategoryTheory Limits Simplicial

namespace SimplexCategory

/-- Every original opposite simplex Hom type is finite by its original unop function. -/
instance finiteOpHom (i j : SimplexCategoryᵒᵖ) : Finite (i ⟶ j) :=
  Finite.of_injective (fun f : i ⟶ j => f.unop) (fun _ _ h => Quiver.Hom.unop_inj h)

/-- The original simplex degree downset is finite at every actual degree. -/
instance finiteReedyBelow (n : ℕ) : Finite (reedy.BelowDegree n) :=
  Finite.of_injective (fun i => (⟨i.val.len, i.property⟩ : Fin n)) (by
    intro i j h
    apply Subtype.ext
    exact SimplexCategory.ext (congrArg Fin.val h))

/-- The opposite simplex degree downset is finite at every actual degree. -/
instance finiteReedyOpBelow (n : ℕ) : Finite (reedyOp.BelowDegree n) :=
  Finite.of_injective (fun i => (⟨i.val.unop.len, i.property⟩ : Fin n)) (by
    intro i j h
    apply Subtype.ext
    apply Opposite.unop_injective
    exact SimplexCategory.ext (congrArg Fin.val h))

/-- The actual cosimplicial latching category is a finite category. -/
instance reedyLatchingFinCategory (j : SimplexCategory) : FinCategory (reedy.Latching j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The actual cosimplicial matching category is a finite category. -/
instance reedyMatchingFinCategory (j : SimplexCategory) : FinCategory (reedy.Matching j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The actual simplicial latching category is a finite category. -/
instance reedyOpLatchingFinCategory (j : SimplexCategoryᵒᵖ) : FinCategory (reedyOp.Latching j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The actual simplicial matching category is a finite category. -/
instance reedyOpMatchingFinCategory (j : SimplexCategoryᵒᵖ) : FinCategory (reedyOp.Matching j) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The original degree-zero cosimplicial latching category is empty. -/
instance reedyLatchingZeroIsEmpty : IsEmpty (reedy.Latching ⦋0⦌) :=
  reedy.latching_isEmpty_of_degree_eq_bot ⦋0⦌ rfl

/-- The original degree-zero cosimplicial matching category is empty. -/
instance reedyMatchingZeroIsEmpty : IsEmpty (reedy.Matching ⦋0⦌) :=
  reedy.matching_isEmpty_of_degree_eq_bot ⦋0⦌ rfl

/-- The original degree-zero simplicial latching category is empty. -/
instance reedyOpLatchingZeroIsEmpty : IsEmpty (reedyOp.Latching (.op ⦋0⦌)) :=
  reedyOp.latching_isEmpty_of_degree_eq_bot (.op ⦋0⦌) rfl

/-- The original degree-zero simplicial matching category is empty. -/
instance reedyOpMatchingZeroIsEmpty : IsEmpty (reedyOp.Matching (.op ⦋0⦌)) :=
  reedyOp.matching_isEmpty_of_degree_eq_bot (.op ⦋0⦌) rfl

namespace ReedyBoundaries

variable {C : Type uC} [Category.{vC} C]

section CosimplicialLatching

variable [HasFiniteColimits C]

/-- The whole actual cosimplicial latching map, using only the original finite colimit. -/
def cosimplicialLatchingMap (X : CosimplicialObject C) (j : SimplexCategory) :
    colimit (reedy.latchingDiagram X j) ⟶ X.obj j :=
  reedy.latchingMapWith X j (colimit.cocone _) (colimit.isColimit _)

/-- Every original direct simplex arrow is recovered by its actual latching injection. -/
@[reassoc]
theorem cosimplicialLatchingMap_ι (X : CosimplicialObject C) (j : SimplexCategory)
    (a : reedy.Latching j) :
    colimit.ι (reedy.latchingDiagram X j) a ≫ cosimplicialLatchingMap X j =
      X.map (reedy.latchingArrow a) :=
  reedy.latchingMapWith_ι X j (colimit.cocone _) (colimit.isColimit _) a

/-- The whole finite latching map is natural in every original cosimplicial map. -/
@[reassoc]
theorem cosimplicialLatchingMap_naturality {X Y : CosimplicialObject C} (f : X ⟶ Y)
    (j : SimplexCategory) :
    cosimplicialLatchingMap X j ≫ f.app j =
      colimMap (reedy.latchingTransformation f j) ≫ cosimplicialLatchingMap Y j := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, cosimplicialLatchingMap_ι, ← Category.assoc, ι_colimMap,
    Category.assoc, cosimplicialLatchingMap_ι]
  exact f.naturality (reedy.latchingArrow a)

end CosimplicialLatching

section CosimplicialMatching

variable [HasFiniteLimits C]

/-- The whole actual cosimplicial matching map, using only the original finite limit. -/
def cosimplicialMatchingMap (X : CosimplicialObject C) (j : SimplexCategory) :
    X.obj j ⟶ limit (reedy.matchingDiagram X j) :=
  reedy.matchingMapWith X j (limit.cone _) (limit.isLimit _)

/-- Every original inverse simplex arrow is recovered by its actual matching projection. -/
@[reassoc]
theorem cosimplicialMatchingMap_π (X : CosimplicialObject C) (j : SimplexCategory)
    (a : reedy.Matching j) :
    cosimplicialMatchingMap X j ≫ limit.π (reedy.matchingDiagram X j) a =
      X.map (reedy.matchingArrow a) :=
  reedy.matchingMapWith_π X j (limit.cone _) (limit.isLimit _) a

/-- The whole finite matching map is natural in every original cosimplicial map. -/
@[reassoc]
theorem cosimplicialMatchingMap_naturality {X Y : CosimplicialObject C} (f : X ⟶ Y)
    (j : SimplexCategory) :
    cosimplicialMatchingMap X j ≫ limMap (reedy.matchingTransformation f j) =
      f.app j ≫ cosimplicialMatchingMap Y j := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, limMap_π, ← Category.assoc, cosimplicialMatchingMap_π,
    Category.assoc, cosimplicialMatchingMap_π]
  exact f.naturality (reedy.matchingArrow a)

end CosimplicialMatching

section SimplicialLatching

variable [HasFiniteColimits C]

/-- The whole actual simplicial latching map, using only the original finite colimit. -/
def simplicialLatchingMap (X : SimplicialObject C) (j : SimplexCategoryᵒᵖ) :
    colimit (reedyOp.latchingDiagram X j) ⟶ X.obj j :=
  reedyOp.latchingMapWith X j (colimit.cocone _) (colimit.isColimit _)

/-- Every original opposite-direct arrow is recovered by its actual latching injection. -/
@[reassoc]
theorem simplicialLatchingMap_ι (X : SimplicialObject C) (j : SimplexCategoryᵒᵖ)
    (a : reedyOp.Latching j) :
    colimit.ι (reedyOp.latchingDiagram X j) a ≫ simplicialLatchingMap X j =
      X.map (reedyOp.latchingArrow a) :=
  reedyOp.latchingMapWith_ι X j (colimit.cocone _) (colimit.isColimit _) a

/-- The whole finite latching map is natural in every original simplicial map. -/
@[reassoc]
theorem simplicialLatchingMap_naturality {X Y : SimplicialObject C} (f : X ⟶ Y)
    (j : SimplexCategoryᵒᵖ) :
    simplicialLatchingMap X j ≫ f.app j =
      colimMap (reedyOp.latchingTransformation f j) ≫ simplicialLatchingMap Y j := by
  apply colimit.hom_ext
  intro a
  rw [← Category.assoc, simplicialLatchingMap_ι, ← Category.assoc, ι_colimMap,
    Category.assoc, simplicialLatchingMap_ι]
  exact f.naturality (reedyOp.latchingArrow a)

end SimplicialLatching

section SimplicialMatching

variable [HasFiniteLimits C]

/-- The whole actual simplicial matching map, using only the original finite limit. -/
def simplicialMatchingMap (X : SimplicialObject C) (j : SimplexCategoryᵒᵖ) :
    X.obj j ⟶ limit (reedyOp.matchingDiagram X j) :=
  reedyOp.matchingMapWith X j (limit.cone _) (limit.isLimit _)

/-- Every original opposite-inverse arrow is recovered by its actual matching projection. -/
@[reassoc]
theorem simplicialMatchingMap_π (X : SimplicialObject C) (j : SimplexCategoryᵒᵖ)
    (a : reedyOp.Matching j) :
    simplicialMatchingMap X j ≫ limit.π (reedyOp.matchingDiagram X j) a =
      X.map (reedyOp.matchingArrow a) :=
  reedyOp.matchingMapWith_π X j (limit.cone _) (limit.isLimit _) a

/-- The whole finite matching map is natural in every original simplicial map. -/
@[reassoc]
theorem simplicialMatchingMap_naturality {X Y : SimplicialObject C} (f : X ⟶ Y)
    (j : SimplexCategoryᵒᵖ) :
    simplicialMatchingMap X j ≫ limMap (reedyOp.matchingTransformation f j) =
      f.app j ≫ simplicialMatchingMap Y j := by
  apply limit.hom_ext
  intro a
  rw [Category.assoc, limMap_π, ← Category.assoc, simplicialMatchingMap_π,
    Category.assoc, simplicialMatchingMap_π]
  exact f.naturality (reedyOp.matchingArrow a)

end SimplicialMatching

end ReedyBoundaries

end SimplexCategory

end
end
end
