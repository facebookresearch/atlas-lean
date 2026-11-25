/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PermutationWordle
import Mathlib.Data.Fintype.Powerset

/-!
# One- and two-guess counts for permutation Wordle

`permWordleCoeff_one_and_two` counts the secrets solved in exactly one or two guesses by
a deranged strategy, by identifying its two-guess solves with supports of size at least two.
-/

namespace MetaMathlibExt
namespace permWordleCoeff_one_and_two

variable {n : ℕ} (S : (m : ℕ) → Equiv.Perm (Fin m))

/-- The second guess determined by the set of incorrect positions in the first guess. -/
private def reply (I : Finset (Fin n)) : Equiv.Perm (Fin n) :=
  (S I.card)⁻¹.extendDomain (I.orderIsoOfFin rfl).toEquiv

private theorem guess_one_eq_reply (π : Equiv.Perm (Fin n)) :
    permWordleGuess S π 1 = ⇑(reply S π.support) := by
  have hI : (Finset.univ.filter fun i => id i ≠ π i) = π.support := by
    ext i
    simp [ne_comm]
  change permuteAlong (Finset.univ.filter fun i => id i ≠ π i) rfl (S _) id = _
  rw [hI]
  funext i
  by_cases hi : i ∈ π.support
  · simp [reply, permuteAlong, hi, Equiv.Perm.extendDomain_apply_subtype _ _ hi]
  · simp [reply, permuteAlong, hi, Equiv.Perm.extendDomain_apply_not_subtype _ _ hi]

private theorem support_reply
    (hS : ∀ m, 2 ≤ m → m ≤ n → ∀ k : Fin m, S m k ≠ k)
    (I : Finset (Fin n)) (hI : 2 ≤ I.card) : (reply S I).support = I := by
  let e := (I.orderIsoOfFin rfl).toEquiv
  have hfull : (S I.card)⁻¹.support = Finset.univ := by
    rw [Equiv.Perm.support_inv]
    exact Finset.eq_univ_of_forall fun k =>
      Equiv.Perm.mem_support.mpr (hS _ hI (card_finset_fin_le I) k)
  change ((S I.card)⁻¹.extendDomain e).support = I
  rw [Equiv.Perm.support_extend_domain, hfull]
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Equiv.asEmbedding_apply]
  exact ⟨fun ⟨k, hk⟩ => hk ▸ (e k).property,
    fun hi => ⟨e.symm ⟨i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩)⟩⟩

private theorem solvedIn_two_iff (π : Equiv.Perm (Fin n)) :
    PermWordleSolvedIn S π 2 ↔ reply S π.support = π ∧ π ≠ 1 := by
  change (1 ≤ 2 ∧ permWordleGuess S π 1 = ⇑π ∧ ∀ j < 1, permWordleGuess S π j ≠ ⇑π) ↔ _
  simp only [Nat.one_le_ofNat, true_and, guess_one_eq_reply, Equiv.coe_inj, Nat.lt_one_iff,
    forall_eq]
  change (_ ∧ ⇑(1 : Equiv.Perm (Fin n)) ≠ ⇑π) ↔ _
  simp only [ne_eq, Equiv.coe_inj, ne_comm (a := π)]

private theorem solvedIn_reply
    (hS : ∀ m, 2 ≤ m → m ≤ n → ∀ k : Fin m, S m k ≠ k)
    (I : Finset (Fin n)) (hI : 2 ≤ I.card) : PermWordleSolvedIn S (reply S I) 2 := by
  have hs := support_reply S hS I hI
  apply (solvedIn_two_iff S _).mpr
  refine ⟨congrArg (reply S) hs, ?_⟩
  intro h
  rw [← hs, h] at hI
  simp at hI

private def supportEquiv
    (hS : ∀ m, 2 ≤ m → m ≤ n → ∀ k : Fin m, S m k ≠ k) :
    {π : Equiv.Perm (Fin n) // PermWordleSolvedIn S π 2} ≃ {I : Finset (Fin n) // 2 ≤ I.card} where
  toFun π := ⟨π.val.support, Equiv.Perm.two_le_card_support_of_ne_one (f := π.val)
    ((solvedIn_two_iff S π.val).mp π.property).2⟩
  invFun I := ⟨reply S I.val, solvedIn_reply S hS I.val I.property⟩
  left_inv π := by
    apply Subtype.ext
    exact ((solvedIn_two_iff S π.val).mp π.property).1
  right_inv I := by
    apply Subtype.ext
    exact support_reply S hS I.val I.property

open Finset in
private theorem card_supports (n : ℕ) :
    Nat.card {I : Finset (Fin n) // 2 ≤ I.card} = 2 ^ n - n - 1 := by
  let small := insert ∅ ((univ : Finset (Fin n)).powersetCard 1)
  have hsmall : small.card = n + 1 := by
    simp [small, card_insert_of_notMem, mem_powersetCard, card_powersetCard]
  have hmem (I : Finset (Fin n)) : I ∈ univ \ small ↔ 2 ≤ I.card := by
    simp only [small, mem_sdiff, mem_univ, true_and, mem_insert, mem_powersetCard_univ,
      ← card_eq_zero]
    omega
  rw [Nat.card_eq_fintype_card, Fintype.card_of_subtype _ hmem,
    card_sdiff_of_subset (subset_univ _), hsmall, card_univ, Fintype.card_finset, Fintype.card_fin]
  omega

end permWordleCoeff_one_and_two

open permWordleCoeff_one_and_two in
/-- **One- and two-guess counts for deranged strategies.** Let $n \in \mathbb{N}$ and let $S$ be
a strategy whose component $S[m]$ has no fixed point for every $2 \le m \le n$, and write
$[x^r] f_S$ for the number of permutations of $\{0, \dots, n-1\}$ that $S$ guesses in exactly $r$
guesses. Then $[x^1] f_S = 1$ and $[x^2] f_S = 2^n - n - 1$, the Eulerian number $A(n, 1)$.

Source: Aurora Hiveley, *Experimenting with Permutation Wordle*, Journal of Integer Sequences 29
(2026), Article 26.1.7, Theorem 5 (`jis-2026-26.1.7-thm-5`). -/
public theorem permWordleCoeff_one_and_two (n : ℕ) (S : (m : ℕ) → Equiv.Perm (Fin m))
    (hS : ∀ m, 2 ≤ m → m ≤ n → ∀ k : Fin m, S m k ≠ k) :
    permWordleCoeff S n 1 = 1 ∧ permWordleCoeff S n 2 = 2 ^ n - n - 1 := by
  classical
  constructor
  · simp [permWordleCoeff, permWordleSolvedIn_one_iff, Nat.card_eq_fintype_card]
  · exact (Nat.card_congr (supportEquiv S hS)).trans (card_supports n)

end MetaMathlibExt
