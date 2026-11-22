/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

-- Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.

module

public import MathlibExt.Combinatorics.TensorNetwork.Presentation

/-! # Bounds for converted tensor-network entries

This module bounds each entry of the complete-graph tensor obtained from a sized factored
network. The label names and decoder are arbitrary: a decoded factor is bounded by size, while a
name outside the selected edge alphabet contributes zero.

Adapted from `eth/proof/networks/Groundwork/Net/Net.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
-/

@[expose] public section

namespace TensorNetwork.Factored

open Finset

variable {J σ τ A : Type*}

/-- A converted tensor entry is a sum of at most `2 ^ P` terms, each containing one weight and
`Fintype.card J - 1` off-diagonal factors. -/
theorem abs_toInstance_le [Fintype J] [LinearOrder J] [DecidableEq A]
    (N : Factored J σ τ) (D : J → J → Finset A) (dec : J → J → A → τ)
    {P B : ℕ} (h : N.Sized P B) (a : J) (theta : J → A) :
    |N.toInstance D dec a theta| ≤ 2 ^ (P + B * Fintype.card J) := by
  unfold toInstance
  have hJ : 0 < Fintype.card J := Fintype.card_pos_iff.2 ⟨a⟩
  have hcard : #(univ.erase a) ≤ Fintype.card J - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ a), Finset.card_univ]
  have hexp : B + B * (Fintype.card J - 1) = B * Fintype.card J := by
    obtain ⟨n, hn⟩ : ∃ n, Fintype.card J = n + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hJ).symm⟩
    rw [hn, Nat.add_sub_cancel]
    ring
  have hprod : ∀ z,
      |∏ b ∈ univ.erase a,
          if theta b ∈ D (min a b) (max a b) then
            N.f a b z (dec (min a b) (max a b) (theta b))
          else 0| ≤ 2 ^ (B * (Fintype.card J - 1)) := by
    intro z
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _b ∈ univ.erase a, (2 : ℤ) ^ B := by
        refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun b _ => ?_
        split_ifs
        · exact h.abs_f _ _ _ _
        · simp
      _ = ((2 : ℤ) ^ B) ^ #(univ.erase a) := by rw [Finset.prod_const]
      _ ≤ ((2 : ℤ) ^ B) ^ (Fintype.card J - 1) :=
        pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hcard
      _ = 2 ^ (B * (Fintype.card J - 1)) := by rw [pow_mul]
  have hterm : ∀ z,
      |N.W a z * ∏ b ∈ univ.erase a,
          if theta b ∈ D (min a b) (max a b) then
            N.f a b z (dec (min a b) (max a b) (theta b))
          else 0| ≤ 2 ^ (B * Fintype.card J) := by
    intro z
    rw [abs_mul, ← hexp, pow_add]
    exact mul_le_mul (h.abs_W a z) (hprod z) (abs_nonneg _)
      (pow_nonneg (by norm_num) _)
  calc
    _ ≤ ∑ z ∈ N.S a,
        |N.W a z * ∏ b ∈ univ.erase a,
          if theta b ∈ D (min a b) (max a b) then
            N.f a b z (dec (min a b) (max a b) (theta b))
          else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ N.S a, (2 : ℤ) ^ (B * Fintype.card J) :=
      Finset.sum_le_sum fun z _ => hterm z
    _ = (#(N.S a) : ℤ) * 2 ^ (B * Fintype.card J) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ P * 2 ^ (B * Fintype.card J) := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) _)
      exact_mod_cast h.card_S a
    _ = 2 ^ (P + B * Fintype.card J) := (pow_add _ _ _).symm

end TensorNetwork.Factored
