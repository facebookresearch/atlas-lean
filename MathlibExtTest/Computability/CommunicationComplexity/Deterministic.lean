/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.CommunicationComplexity.Deterministic

/-!
# Tests for deterministic communication complexity
-/

namespace MathlibExtTest.Computability.CommunicationComplexity

open MathlibExt.Computability.CommunicationComplexity
open MathlibExt.Computability.CommunicationComplexity.Protocol

/-- The diagonal is a fooling set for equality, with value `true`. -/
theorem isFoolingSet_diag (n : ℕ) :
    IsFoolingSet (eqFn n) (Finset.univ.image fun x : Fin n → Bool => (x, x)) true := by
  refine ⟨?_, ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
    simp [eqFn]
  · intro s hs t ht hst
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 ht
    left
    have : x ≠ y := fun h => hst (by rw [h])
    simp [eqFn, this]

/-- The fooling-set bound gives `2 ^ n ≤ 2 ^ D(EQ_n)` for every `n`, including `n = 0`. -/
example (n : ℕ) : 2 ^ n ≤ 2 ^ commComplexity (eqFn n) := by
  have h := card_le_two_pow_commComplexity (isFoolingSet_diag n)
  rwa [Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).1), Finset.card_univ,
    Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h

/-- The communication matrix of equality is the identity matrix. -/
theorem commMatrix_eqFn (n : ℕ) : commMatrix ℚ (eqFn n) = 1 := by
  ext x y
  by_cases h : x = y <;> simp [commMatrix, eqFn, Matrix.one_apply, h]

/-- The rank bound applied to equality: `rank I = 2 ^ n`, so `n ≤ D(EQ_n)`. -/
example (n : ℕ) : n ≤ commComplexity (eqFn n) := by
  have h := log_rank_le_commComplexity ℚ (eqFn n)
  rwa [commMatrix_eqFn, Matrix.rank_one, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.clog_pow _ _ (by norm_num)] at h

/-- Equality of two-bit strings needs exactly three bits. -/
example : commComplexity (eqFn 2) = 3 := commComplexity_eqFn (by norm_num)

/-- Equality of zero-bit strings needs no communication (the degenerate case). -/
example : commComplexity (eqFn 0) = 0 := commComplexity_eqFn_zero

/-- A one-bit protocol: Alice announces her bit, for the function `f x y = x`. -/
example : (alice (fun x : Bool => x) (output false) (output true) : Protocol Bool Bool).Computes
    (fun x _ => x) := by
  intro x y; cases x <;> rfl

/-- The trivial equality protocol on three bits has depth at most four. -/
example : (eqProtocol 3).depth ≤ 4 := depth_eqProtocol_le 3

/-- The leaves of a protocol tree are counted by the depth bound, here `2` leaves at depth `1`. -/
example : (alice (fun x : Bool => x) (output false) (output true) :
    Protocol Bool Bool).leaves.card = 2 := by decide

/-- The log-rank conjecture is a proposition only (no proof is claimed). -/
example : Prop := LogRankConjecture

end MathlibExtTest.Computability.CommunicationComplexity
