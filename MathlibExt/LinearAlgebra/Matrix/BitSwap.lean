/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: expressed the crossing using Mathlib permutation matrices and the
identity using `Matrix.one`, extracted the grouped decomposition, and added reuse tests.
-/
module

public import Mathlib.Data.Matrix.PEquiv
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Bounds

/-! # Bit-swap decomposition

Swapping two bits is the identity minus the outer product of the unnormalized antisymmetric
vector `(0, 1, -1, 0)`. Products of these identities can be grouped by the number of
antisymmetric factors, giving `n + 1` pieces for swapping two `n`-bit strings.

Adapted from `eth/proof/networks/Groundwork/Cross/Bit.lean` and the uncrossing definitions in
`eth/proof/statements/NetworkStatements.lean` in
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.
This is the source's single-bit variant. The paper's principal construction instead uses
three-bit blocks and the eight-square identity. No rank or algorithmic time bound is asserted here.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace Matrix

open Finset

/-- The unnormalized antisymmetric two-bit vector, in order `00, 01, 10, 11`. -/
def bitSinglet (p : Bool × Bool) : ℤ :=
  if p.1 = p.2 then 0 else if p.1 then -1 else 1

/-- The one-bit swap matrix is the identity minus the singlet outer product. -/
theorem bitSwap_eq_one_sub_vecMulVec :
    (Equiv.prodComm Bool Bool).toPEquiv.toMatrix =
      (1 : Matrix (Bool × Bool) (Bool × Bool) ℤ) - vecMulVec bitSinglet bitSinglet := by
  ext ⟨x, y⟩ ⟨u, v⟩
  cases x <;> cases y <;> cases u <;> cases v <;> decide

/-- The part of an `n`-bit swap with exactly `i` antisymmetric factors. -/
def bitSwapPiece (n i : ℕ) :
    Matrix ((Fin n → Bool) × (Fin n → Bool)) ((Fin n → Bool) × (Fin n → Bool)) ℤ :=
  fun p q => ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
    (∏ k ∈ S, -(bitSinglet (p.1 k, p.2 k) * bitSinglet (q.1 k, q.2 k))) *
      ∏ k ∈ Sᶜ, (1 : Matrix (Bool × Bool) (Bool × Bool) ℤ)
        (p.1 k, p.2 k) (q.1 k, q.2 k)

private theorem swap_apply {α : Type*} [DecidableEq α] (x y u v : α) :
    (Equiv.prodComm α α).toPEquiv.toMatrix (x, y) (u, v) =
      (if x = v ∧ y = u then 1 else 0 : ℤ) := by
  simp [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, and_comm]

private theorem swap_entry_eq_prod {n : ℕ} (x y u v : Fin n → Bool) :
    (Equiv.prodComm (Fin n → Bool) (Fin n → Bool)).toPEquiv.toMatrix (x, y) (u, v) =
      ∏ k, ((Equiv.prodComm Bool Bool).toPEquiv.toMatrix (x k, y k) (u k, v k) : ℤ) := by
  simp_rw [swap_apply]
  by_cases h : x = v ∧ y = u
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [ite_eq_right h]
    have hex : ∃ k, ¬ (x k = v k ∧ y k = u k) := by
      by_contra hc
      push Not at hc
      exact h ⟨funext fun k => (hc k).1, funext fun k => (hc k).2⟩
    obtain ⟨k, hk⟩ := hex
    exact (prod_eq_zero (mem_univ k) (by simp only [ite_eq_right hk])).symm

/-- The `n + 1` grouped pieces sum to the permutation matrix swapping the two bit strings. -/
theorem sum_bitSwapPiece (n : ℕ) (p q : (Fin n → Bool) × (Fin n → Bool)) :
    ∑ i ∈ range (n + 1), bitSwapPiece n i p q =
      (Equiv.prodComm (Fin n → Bool) (Fin n → Bool)).toPEquiv.toMatrix p q := by
  rcases p with ⟨x, y⟩
  rcases q with ⟨u, v⟩
  have h (k : Fin n) :
      ((Equiv.prodComm Bool Bool).toPEquiv.toMatrix (x k, y k) (u k, v k) : ℤ) =
        -(bitSinglet (x k, y k) * bitSinglet (u k, v k)) +
          (1 : Matrix (Bool × Bool) (Bool × Bool) ℤ) (x k, y k) (u k, v k) := by
    rw [bitSwap_eq_one_sub_vecMulVec]
    change _ - _ * _ = -(_ * _) + _
    ring
  rw [swap_entry_eq_prod]
  simp_rw [h]
  rw [prod_add, sum_powerset, card_univ, Fintype.card_fin]
  simp only [bitSwapPiece, compl_eq_univ_sdiff]

/-- There is no piece containing more antisymmetric factors than bit positions. -/
theorem bitSwapPiece_eq_zero_of_lt {n i : ℕ} (h : n < i) : bitSwapPiece n i = 0 := by
  have hs : powersetCard i (univ : Finset (Fin n)) = ∅ :=
    powersetCard_eq_empty.mpr (by simpa using h)
  funext p q
  simp [bitSwapPiece, hs]

private theorem abs_prod_le_one {ι : Type*} (S : Finset ι) (f : ι → ℤ)
    (h : ∀ k, |f k| ≤ 1) : |∏ k ∈ S, f k| ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert k S hk ih =>
    rw [prod_insert hk, abs_mul]
    simpa using mul_le_mul (h k) ih (abs_nonneg _) (by decide : (0 : ℤ) ≤ 1)

/-- Each entry of the `i`th piece is bounded by the number of `i`-subsets of the bit positions. -/
theorem abs_bitSwapPiece_le_choose (n i : ℕ) (p q : (Fin n → Bool) × (Fin n → Bool)) :
    |bitSwapPiece n i p q| ≤ (n.choose i : ℤ) := by
  have h1 : ∀ a b : Bool × Bool, |-(bitSinglet a * bitSinglet b)| ≤ 1 := by decide
  have h0 : ∀ a b : Bool × Bool, |(1 : Matrix (Bool × Bool) (Bool × Bool) ℤ) a b| ≤ 1 :=
    by decide
  unfold bitSwapPiece
  calc
    _ ≤ ∑ S ∈ powersetCard i (univ : Finset (Fin n)),
        |(∏ k ∈ S, -(bitSinglet (p.1 k, p.2 k) * bitSinglet (q.1 k, q.2 k))) *
          ∏ k ∈ Sᶜ, (1 : Matrix (Bool × Bool) (Bool × Bool) ℤ)
            (p.1 k, p.2 k) (q.1 k, q.2 k)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ powersetCard i (univ : Finset (Fin n)), (1 : ℤ) := by
      refine sum_le_sum fun S _ => ?_
      rw [abs_mul]
      simpa using mul_le_mul (abs_prod_le_one S _ (fun k => h1 _ _))
        (abs_prod_le_one Sᶜ _ (fun k => h0 _ _)) (abs_nonneg _) (by decide : (0 : ℤ) ≤ 1)
    _ = (n.choose i : ℤ) := by simp

/-- The uniform entry bound used in the source: every piece has absolute value at most `2 ^ n`. -/
theorem abs_bitSwapPiece_le_two_pow (n i : ℕ)
    (p q : (Fin n → Bool) × (Fin n → Bool)) : |bitSwapPiece n i p q| ≤ 2 ^ n :=
  (abs_bitSwapPiece_le_choose n i p q).trans (by exact_mod_cast Nat.choose_le_two_pow n i)

end Matrix
