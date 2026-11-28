/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

-- Author: @toskua
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

/-!
# Face and degeneracy maps of a simplicial group

For `G : SimplicialObject GrpCat.{u}`, forgetting the group structure gives a simplicial set
whose simplices in each degree carry the group structure of `G` in that degree. Every
simplicial operator preserves multiplication, inverses, and the identity. For `i : Fin (n +
1)`, the two matching faces of the degeneracy `σ i` are the identity: `δ (Fin.castSucc i) (σ i
x) = x` and `δ i.succ (σ i x) = x`.
-/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

variable (G : SimplicialObject GrpCat.{u})

/-- For `G : SimplicialObject GrpCat.{u}`, the simplicial set `underlying G : SSet.{u}` is `G ⋙
forget GrpCat`. At each `n : SimplexCategoryᵒᵖ`, its simplices are the elements of the group
`G.obj n`, and its simplicial operators are the underlying functions of `G.map`. -/
def underlying : SSet.{u} := G ⋙ forget GrpCat

/-- For `G : SimplicialObject GrpCat.{u}` and `n : SimplexCategoryᵒᵖ`, the group structure on
`(underlying G).obj n` is the structure on `G.obj n` under the forgetful functor.
Multiplication, inverse, and identity are therefore those of the degree group of `G`. -/
local instance underlyingGroup (n : SimplexCategoryᵒᵖ) : Group ((underlying G).obj n) :=
  inferInstanceAs (Group (G.obj n))

/-- For `G : SimplicialObject GrpCat.{u}`, an arrow `α : n ⟶ m` in `SimplexCategoryᵒᵖ`, and `x, y ∈ (underlying G).obj n`,
`(underlying G).map α (x * y) = (underlying G).map α x * (underlying G).map α y`.
This is the multiplicativity of the group homomorphism `G.map α`. -/
theorem operator_mul {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (x y : (underlying G).obj n) :
    (underlying G).map α (x * y) = (underlying G).map α x * (underlying G).map α y :=
  (G.map α).hom.map_mul x y

/-- For `G : SimplicialObject GrpCat.{u}`, `α : n ⟶ m` in `SimplexCategoryᵒᵖ`, and `x ∈ (underlying G).obj n`,
`(underlying G).map α x⁻¹ = ((underlying G).map α x)⁻¹`. -/
theorem operator_inv {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (x : (underlying G).obj n) :
    (underlying G).map α x⁻¹ = ((underlying G).map α x)⁻¹ := (G.map α).hom.map_inv x

/-- For `G : SimplicialObject GrpCat.{u}` and `α : n ⟶ m` in `SimplexCategoryᵒᵖ`,
`(underlying G).map α (1 : (underlying G).obj n) = 1`,
where the identity on the right belongs to the degree group at `m`. -/
theorem operator_one {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (underlying G).map α (1 : (underlying G).obj n) = 1 := (G.map α).hom.map_one

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 1)`, and `x ∈ (underlying G) _⦋n⦌`,
`(underlying G).δ (Fin.castSucc i) ((underlying G).σ i x) = x`.
Thus the face at index `i`, viewed in `Fin (n + 2)`, is a left inverse of the degeneracy at `i`. -/
theorem face_degeneracy_self {n : ℕ} (i : Fin (n + 1)) (x : (underlying G) _⦋n⦌) :
    (underlying G).δ (Fin.castSucc i) ((underlying G).σ i x) = x :=
  ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_self (i := i)) x

/-- For `G : SimplicialObject GrpCat.{u}`, `n : ℕ`, `i : Fin (n + 1)`, and `x ∈ (underlying G) _⦋n⦌`,
`(underlying G).δ i.succ ((underlying G).σ i x) = x`.
The face immediately after `i` is also a left inverse of the degeneracy at `i`. -/
theorem face_degeneracy_succ {n : ℕ} (i : Fin (n + 1)) (x : (underlying G) _⦋n⦌) :
    (underlying G).δ i.succ ((underlying G).σ i x) = x :=
  ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_succ (i := i)) x

end SSet.SimplicialGroupHorn
