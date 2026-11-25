/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.Basic

/-!
# Independent-index and ordered-action clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe um un up uq uR uS

namespace Matrix.LocallyFinite.SourceClients.Basic

variable {m : Type um} {n : Type un} {p : Type up} {q : Type uq}
  {R : Type uR} {S : Type uS}

/-- The original free-left-module row action places the input scalar on the left. -/
theorem scalar_order [Semiring R] (A : Matrix.LocallyFinite m n R)
    (i : m) (r : R) (j : n) : A.rowAction (Finsupp.single i r) j = r * A i j := by
  rw [rowAction_single, Finsupp.smul_apply, row_apply, smul_eq_mul]

/-- Four independently sized index worlds retain the original triple product. -/
theorem independent_triple_product [Semiring R] (A : Matrix.LocallyFinite m n R)
    (B : Matrix.LocallyFinite n p R) (C : Matrix.LocallyFinite p q R) :
    (A.comp B).comp C = A.comp (B.comp C) := comp_assoc A B C

/-- The action of the actual product is the second original action after the first. -/
theorem action_order [Semiring R] (A : Matrix.LocallyFinite m n R)
    (B : Matrix.LocallyFinite n p R) (x : m →₀ R) :
    (A.comp B).rowAction x = B.rowAction (A.rowAction x) := by
  rw [rowAction_comp]
  rfl

/-- An actual nonzero product entry has an actual nonzero original factor pair. -/
theorem contributing_index [Semiring R] (A : Matrix.LocallyFinite m n R)
    (B : Matrix.LocallyFinite n p R) (i : m) (j : p) (h : A.comp B i j ≠ 0) :
    ∃ k, A i k ≠ 0 ∧ B k j ≠ 0 := exists_comp_term A B i j h

/-- The coefficient and both index universes remain independent in the exact row reader. -/
theorem independent_mapped_row [Zero R] [Zero S] (f : ZeroHom R S)
    (A : Matrix.LocallyFinite m n R) (i : m) (j : n) :
    (Matrix.LocallyFinite.map f A).row i j = f (A i j) := rfl

end Matrix.LocallyFinite.SourceClients.Basic

end
