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
abbrev underlying : SSet.{u} := G ⋙ forget GrpCat

/-- For `G : SimplicialObject GrpCat.{u}` and `n : SimplexCategoryᵒᵖ`, the group structure on
`(underlying G).obj n` is the structure on `G.obj n` under the forgetful functor.
Multiplication, inverse, and identity are therefore those of the degree group of `G`. -/
local instance underlyingGroup (n : SimplexCategoryᵒᵖ) : Group ((underlying G).obj n) :=
  inferInstanceAs (Group (G.obj n))

end SSet.SimplicialGroupHorn
