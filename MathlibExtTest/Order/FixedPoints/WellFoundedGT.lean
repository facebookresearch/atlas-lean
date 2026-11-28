/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Order.FixedPoints.WellFoundedGT
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Order

/-! # Tests for Kleene iteration under the ascending chain condition -/

/-- `ℕ∞ᵒᵈ`, the order dual of `ℕ ∪ {∞}`, is an infinite complete lattice with no infinite strictly
ascending chain but with chains of every finite length, so it has no finite height. Every monotone
map on it still reaches its least fixed point after finitely many iterations from `⊥`. -/
example (f : ℕ∞ᵒᵈ →o ℕ∞ᵒᵈ) : ∃ k, f^[k] ⊥ = f.lfp :=
  (OrderHom.lfp_eq_iSup_iterate_of_wellFoundedGT f).2

/-- On `ℕ∞ᵒᵈ`, the map `x ↦ x ⊔ toDual 3` has iterates `⊥, toDual 3, toDual 3, …` from `⊥`, so the
supremum formula gives its least fixed point `toDual 3`. -/
example : (⟨fun x => x ⊔ OrderDual.toDual 3, fun _ _ h => sup_le_sup_right h _⟩ :
    ℕ∞ᵒᵈ →o ℕ∞ᵒᵈ).lfp = OrderDual.toDual 3 := by
  set f : ℕ∞ᵒᵈ →o ℕ∞ᵒᵈ := ⟨fun x => x ⊔ OrderDual.toDual 3, fun _ _ h => sup_le_sup_right h _⟩
  have hle : ∀ n, f^[n] ⊥ ≤ OrderDual.toDual 3 := fun n => by
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact sup_le ih le_rfl
  rw [(OrderHom.lfp_eq_iSup_iterate_of_wellFoundedGT f).1]
  refine le_antisymm (iSup_le hle) ?_
  exact le_sup_right.trans (le_iSup (fun n => f^[n] ⊥) 1)

/-- On the finite lattice `Bool`, the iterates of the constant map `true` from `⊥ = false` are
`false, true, true, …`, so the supremum formula gives its least fixed point `true`. -/
example : (OrderHom.const Bool true).lfp = true := by
  rw [(OrderHom.lfp_eq_iSup_iterate_of_wellFoundedGT _).1]
  exact top_unique (le_iSup (fun n => (OrderHom.const Bool true)^[n] ⊥) 1)
