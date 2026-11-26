/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.ReverseDivisor
public import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card

/-!
# Sufficient conditions for a multiple with divisible reversal

A natural number coprime to ten has a repunit multiple, whose decimal reversal is
itself; a decimal palindrome or a reverse divisor already divides the reversal of
itself. In each case there is a multiple whose decimal reversal is divisible by
the number.

Statements from Mohamed Ayad and Rachid Bouchenna,
"Which Integer Divides the Reverse of Any of Its
Multiples?", *INTEGERS* 25 (2025), Article A37
(<https://math.colgate.edu/~integers/vol25.html>).
-/

public section

namespace MathlibExt.NumberTheory.Digits.ReverseDivisorWanted

private def repunit (t : ℕ) : ℕ :=
  Nat.ofDigits 10 (List.replicate t 1)

private theorem repunit_add (i d : ℕ) :
    repunit (i + d) = repunit i + 10 ^ i * repunit d := by
  unfold repunit
  rw [List.replicate_add i d 1, Nat.ofDigits_append, List.length_replicate]

private theorem repunit_pos (t : ℕ) (ht : 1 ≤ t) : 1 ≤ repunit t := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  unfold repunit
  rw [List.replicate_succ, Nat.ofDigits_cons]
  omega

private theorem repunit_digits (t : ℕ) :
    Nat.digits 10 (repunit t) = List.replicate t 1 := by
  unfold repunit
  apply Nat.digits_ofDigits 10 (by decide) _ _ _
  · intro l hl
    rw [List.eq_of_mem_replicate hl]
    decide
  · intro h
    rw [List.getLast_replicate h]
    decide

private theorem reverse_repunit (t : ℕ) :
    Nat.reverseDigits 10 (repunit t) = repunit t := by
  unfold Nat.reverseDigits
  rw [repunit_digits, List.reverse_replicate]
  rfl

private theorem repunit_dvd_of_lt_modEq (n i j : ℕ) (hCop : Nat.Coprime n 10)
    (hlt : i < j) (heq : repunit i % n = repunit j % n) :
    n ∣ repunit (j - i) := by
  have hle : i ≤ j := Nat.le_of_lt hlt
  have hj : i + (j - i) = j := Nat.add_sub_cancel' hle
  have hsplit : repunit j = repunit i + 10 ^ i * repunit (j - i) := by
    conv_lhs => rw [← hj]
    exact repunit_add i (j - i)
  have hmod : repunit i ≡ repunit j [MOD n] := heq
  have hdvd : n ∣ repunit j - repunit i := hmod.dvd'
  rw [hsplit, Nat.add_sub_cancel_left] at hdvd
  have hCopPow : Nat.Coprime n (10 ^ i) := by
    have h := hCop.pow 1 i
    simpa [pow_one] using h
  exact hCopPow.dvd_of_dvd_mul_left hdvd

private theorem exists_dvd_repunit (n : ℕ) (hCop : Nat.Coprime n 10) :
    ∃ t : ℕ, 1 ≤ t ∧ n ∣ repunit t := by
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    simp [Nat.Coprime] at hCop
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hcard : (Finset.range n).card < (Finset.range (n + 1)).card := by
    simp [Finset.card_range]
  have hmaps : Set.MapsTo (fun i => repunit i % n)
      (↑(Finset.range (n + 1))) (↑(Finset.range n)) := by
    intro x _
    simp only [Finset.coe_range]
    exact Nat.mod_lt _ hnpos
  obtain ⟨i, _, j, _, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  by_cases hlt : i < j
  · exact ⟨j - i, by omega, repunit_dvd_of_lt_modEq n i j hCop hlt heq⟩
  · have hlt' : j < i := by omega
    have heq' : repunit j % n = repunit i % n := heq.symm
    exact ⟨i - j, by omega, repunit_dvd_of_lt_modEq n j i hCop hlt' heq'⟩

/-- **Sufficient conditions for a multiple with divisible reversal.** Let $n$ be a natural
number such that $\gcd(n, 10) = 1$, or $n$ equals its decimal reversal, or $n$ is a reverse
divisor. Then there is a natural number $k_0 \ge 1$ such that $n$ divides the decimal reversal
of $k_0 n$.

Source: Mohamed Ayad and Rachid Bouchenna, "Which
Integer Divides the Reverse of Any of Its Multiples?",
Proposition 6. -/
theorem exists_dvd_reverseDigits_mul (n : ℕ)
    (h : Nat.Coprime n 10 ∨ Nat.reverseDigits 10 n = n ∨
      IsReverseDivisor n) :
    ∃ k₀ : ℕ, 1 ≤ k₀ ∧ n ∣ Nat.reverseDigits 10 (k₀ * n) := by
  rcases h with hCop | hpal | hdiv
  · obtain ⟨t, ht1, hdvd⟩ := exists_dvd_repunit n hCop
    obtain ⟨k₀, hk₀⟩ := hdvd
    have hRpos : 1 ≤ repunit t := repunit_pos t ht1
    have hk₀ne : k₀ ≠ 0 := by
      intro h0
      rw [h0, Nat.mul_zero] at hk₀
      omega
    have hk₀pos : 1 ≤ k₀ := Nat.pos_of_ne_zero hk₀ne
    have hrev : Nat.reverseDigits 10 (repunit t) = repunit t :=
      reverse_repunit t
    have hEq : k₀ * n = repunit t := by
      rw [hk₀, Nat.mul_comm]
    refine ⟨k₀, hk₀pos, ?_⟩
    rw [hEq, hrev]
    exact ⟨k₀, hk₀⟩
  · exact ⟨1, le_rfl, by simp [one_mul, hpal]⟩
  · obtain ⟨hn, k, hk, hrev⟩ := hdiv
    refine ⟨1, le_rfl, ?_⟩
    rw [one_mul, hrev]
    exact dvd_mul_left n k

end MathlibExt.NumberTheory.Digits.ReverseDivisorWanted
