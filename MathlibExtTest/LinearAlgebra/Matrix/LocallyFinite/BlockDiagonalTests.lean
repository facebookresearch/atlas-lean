/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.Matrix.LocallyFinite.BlockDiagonal

/-!
# Original block coordinates and row-action return clients
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

universe uκ um un up uR

namespace Matrix.LocallyFinite.SourceClients.BlockDiagonal

variable {κ : Type uκ} {m : Type um} {n : Type un} {p : Type up} {R : Type uR}

/-- The actual block product reads the original independently sized rectangular block product. -/
theorem original_block_product [Semiring R] (A : κ → Matrix.LocallyFinite m n R)
    (B : κ → Matrix.LocallyFinite n p R) (k : κ) (i : m) (j : p) :
    (blockDiagonal A).comp (blockDiagonal B) (k, i) (k, j) = (A k).comp (B k) i j := by
  rw [blockDiagonal_comp, blockDiagonal_apply_same]

/-- Infinite original block indices retain the actual identity, with no finiteness input. -/
theorem infinite_block_identity [Semiring R] :
    blockDiagonal (fun _ : ℕ => (1 : Matrix.LocallyFinite m m R)) = 1 := blockDiagonal_one

/-- The original row action of the injected summand has the actual projection return map. -/
theorem original_row_action_return [Semiring R] (e : m ↪ n) :
    (inclusion (R := R) e).rowAction.comp (projection e).rowAction = LinearMap.id := by
  rw [← rowAction_comp, projection_comp_inclusion, rowAction_one]

/-- An actual disjoint original summand has zero mixed row action. -/
theorem disjoint_row_action_zero [Semiring R] (e : m ↪ n) (f : p ↪ n)
    (h : Disjoint (Set.range e) (Set.range f)) :
    (inclusion (R := R) e).rowAction.comp (projection f).rowAction = 0 := by
  rw [← rowAction_comp, projection_comp_inclusion_of_disjoint e f h, rowAction_zero]

end Matrix.LocallyFinite.SourceClients.BlockDiagonal

end
