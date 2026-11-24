/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.Reedy.SimplexCategory
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import MathlibExt.CategoryTheory.Reedy.FiniteBoundaries

/-!
# The original simplex category and its opposite are Reedy

The degree is the simplex length and the direct and inverse classes come from
Mathlib's `SimplexCategory.reedyStructure`. The chosen factor record uses the
explicit epi–image–mono maps and agrees with the native factorization.

The two structures have finite latching and matching categories. Use the generic
`CategoryTheory.ReedyStructure.latchingMap` and `matchingMap` (and their
leg and naturality theorems) with these finite shapes.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

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

end SimplexCategory

end
end
end
