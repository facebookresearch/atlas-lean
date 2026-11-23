/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-- **Cassini's identity for Pell numbers.** Let $(P_n)_{n \ge 0}$ be the Pell numbers, the
natural numbers with $P_0 = 0$, $P_1 = 1$ and $P_{n+2} = 2P_{n+1} + P_n$ for every $n \ge 0$.
Then for every natural number $k \ge 1$,
$$
P_{k-1} P_{k+1} = P_k^2 + (-1)^k.
$$

Source: aBa Mbirika, Janee Schrader, and Jürgen Spilker, "Pell and Associated
Pell Braid Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and
Related Numbers," Journal of Integer Sequences 26 (2023), Article 23.6.4,
Lemma (label lem:Cassini_identity_Pell_version), lines 367–369,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Mbirika/mbir5.tex>; attributed
there to Horadam, Identity (30).
Proves `Wanted` entry `pell_cassini_identity`. -/
theorem pell_cassini_identity
    (P : ℕ → ℕ)
    (hP_zero : P 0 = 0)
    (hP_one : P 1 = 1)
    (hP_step : ∀ n : ℕ, P (n + 2) = 2 * P (n + 1) + P n)
    (k : ℕ)
    (hk : 1 ≤ k) :
    (P (k - 1) : ℤ) * (P (k + 1) : ℤ) =
      (P k : ℤ) ^ 2 + (-1 : ℤ) ^ k := by
  have cstep : ∀ m : ℕ, (P (m + 2) : ℤ) =
      2 * (P (m + 1) : ℤ) + (P m : ℤ) :=
    fun m => by exact_mod_cast hP_step m
  have base : (P 0 : ℤ) * (P 2 : ℤ) - (P 1 : ℤ) ^ 2 = -(-1 : ℤ) ^ 0 := by
    rw [hP_zero, hP_one]
    norm_num
  have step : ∀ j : ℕ, (P (j + 1) : ℤ) * (P (j + 3) : ℤ) -
      (P (j + 2) : ℤ) ^ 2 =
      -((P j : ℤ) * (P (j + 2) : ℤ) - (P (j + 1) : ℤ) ^ 2) := by
    intro j
    have r1 := cstep j
    have r2 := cstep (j + 1)
    have e1 : j + 1 + 2 = j + 3 := by omega
    have e2 : j + 1 + 1 = j + 2 := by omega
    rw [e1, e2] at r2
    linear_combination (P (j + 1) : ℤ) * r2 - (P (j + 2) : ℤ) * r1
  have E : ∀ j : ℕ, (P j : ℤ) * (P (j + 2) : ℤ) - (P (j + 1) : ℤ) ^ 2 =
      -(-1 : ℤ) ^ j := by
    intro j
    induction j with
    | zero =>
      have e1 : 0 + 2 = 2 := by omega
      have e2 : 0 + 1 = 1 := by omega
      rw [e1, e2]
      exact base
    | succ j ih =>
      have e1 : j + 1 + 2 = j + 3 := by omega
      have e2 : j + 1 + 1 = j + 2 := by omega
      rw [e1, e2]
      have pw : (-1 : ℤ) ^ (j + 1) = -(-1 : ℤ) ^ j := by
        rw [pow_succ]
        ring
      rw [step j, ih, pw]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e0 : 1 + m - 1 = m := by omega
  have e1 : 1 + m + 1 = m + 2 := by omega
  have e2 : 1 + m = m + 1 := by omega
  rw [e0, e1, e2]
  have pw : (-1 : ℤ) ^ (m + 1) = -(-1 : ℤ) ^ m := by
    rw [pow_succ]
    ring
  rw [pw]
  have hE := E m
  linear_combination hE

end MetaMathlibExt
