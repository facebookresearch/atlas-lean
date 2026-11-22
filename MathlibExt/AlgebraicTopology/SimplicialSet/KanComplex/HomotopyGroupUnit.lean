/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup

/-!
# The canonical unit of positive homotopy groups

The group structure in positive degree uses the constant pointed simplex as
its unit. This public characteristic follows from the multiplication-triangle
interface and preserves the opacity of the group construction.
-/

@[expose] public section

universe u

open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.KanComplex.π

variable {n : ℕ} {X : SSet.{u}} [KanComplex X] {x : X _⦋0⦌}

/-- The selected positive-degree group uses the existing all-degree unit. -/
@[simp]
lemma group_one_eq_instOne :
    (group (n := n) (X := X) (x := x)).one =
      (instOne (n := n + 1) (X := X) (x := x)).one := by
  let e := (instOne (n := n + 1) (X := X) (x := x)).one
  let g := (group (n := n) (X := X) (x := x)).one
  have he : e * g = g := by
    obtain ⟨p, hp⟩ := mk_surjective g
    rw [← hp]
    exact mul_eq_of_mulStruct' (PtSimplex.MulStruct.oneMul p (Fin.last n))
  exact he.symm.trans (mul_one e)

end SSet.KanComplex.π
