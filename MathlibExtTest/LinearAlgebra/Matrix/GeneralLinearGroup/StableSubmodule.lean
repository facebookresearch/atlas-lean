/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.StableSubmodule

open Matrix Matrix.GeneralLinearGroup

-- Over `ℚ`, a `GL₃(ℚ)`-stable proper subspace of `ℚ³` is zero.
example (W : Submodule ℚ (Fin 3 → ℚ))
    (hW : ∀ g : GL (Fin 3) ℚ, ∀ x ∈ W, (g : Matrix (Fin 3) (Fin 3) ℚ) *ᵥ x ∈ W) (h : W ≠ ⊤) :
    W = ⊥ :=
  (eq_bot_or_eq_top_of_forall_mulVec_mem W hW).resolve_right h

-- The one-dimensional case: every subspace of `K¹` is `⊥` or `⊤`.
example (W : Submodule (ZMod 2) (Fin 1 → ZMod 2))
    (hW : ∀ g : GL (Fin 1) (ZMod 2), ∀ x ∈ W, (g : Matrix (Fin 1) (Fin 1) (ZMod 2)) *ᵥ x ∈ W) :
    W = ⊥ ∨ W = ⊤ :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  eq_bot_or_eq_top_of_forall_mulVec_mem W hW

-- For `p = 3`, a `GL₂(ℤ/3ℤ)`-stable subgroup of `(ℤ/3ℤ)²` does not have order `3`.
example (H : AddSubgroup (Fin 2 → ZMod 3))
    (hH : ∀ g : GL (Fin 2) (ZMod 3), ∀ x ∈ H, (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) *ᵥ x ∈ H) :
    Nat.card H ≠ 3 :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  natCard_ne_of_forall_mulVec_mem H hH

-- The whole group is stable, so its order (`4`) is not `2`.
example : Nat.card (⊤ : AddSubgroup (Fin 2 → ZMod 2)) ≠ 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  natCard_ne_of_forall_mulVec_mem ⊤ fun _ _ _ => AddSubgroup.mem_top _
