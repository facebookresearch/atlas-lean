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

/-! # The actual whole face and degeneracy group maps of an original simplicial group -/

@[expose] public section

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.SimplicialGroupHorn

variable (G : SimplicialObject GrpCat.{u})

/-- The SAME original simplicial group has its actual underlying scalar simplicial set. -/
def underlying : SSet.{u} := G ⋙ forget GrpCat

/-- The exact original degree group is scoped on the SAME underlying scalar carrier. -/
local instance underlyingGroup (n : SimplexCategoryᵒᵖ) : Group ((underlying G).obj n) :=
  inferInstanceAs (Group (G.obj n))

/-- Every full original simplex operator preserves multiplication as its genuine group morphism. -/
theorem operator_mul {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (x y : (underlying G).obj n) :
    (underlying G).map α (x * y) = (underlying G).map α x * (underlying G).map α y :=
  (G.map α).hom.map_mul x y

/-- Every original operator preserves the actual inverse, before any Kan assertion. -/
theorem operator_inv {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) (x : (underlying G).obj n) :
    (underlying G).map α x⁻¹ = ((underlying G).map α x)⁻¹ := (G.map α).hom.map_inv x

/-- The complete original group unit is retained by every actual simplex operator. -/
theorem operator_one {n m : SimplexCategoryᵒᵖ} (α : n ⟶ m) :
    (underlying G).map α (1 : (underlying G).obj n) = 1 := (G.map α).hom.map_one

/-- The whole original face after its matching degeneracy is the actual identity. -/
theorem face_degeneracy_self {n : ℕ} (i : Fin (n + 1)) (x : (underlying G) _⦋n⦌) :
    (underlying G).δ (Fin.castSucc i) ((underlying G).σ i x) = x :=
  ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_self (i := i)) x

/-- The other original matching face retains the SAME actual degeneracy inverse equation. -/
theorem face_degeneracy_succ {n : ℕ} (i : Fin (n + 1)) (x : (underlying G) _⦋n⦌) :
    (underlying G).δ i.succ ((underlying G).σ i x) = x :=
  ConcreteCategory.congr_hom ((underlying G).δ_comp_σ_succ (i := i)) x

end SSet.SimplicialGroupHorn
