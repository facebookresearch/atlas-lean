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

/-- **Cassini's identity for associated Pell numbers.** Let $(Q_n)_{n \ge 0}$ be a sequence of
integers with $Q_0 = Q_1 = 1$ and $Q_{n+2} = 2Q_{n+1} + Q_n$ for every $n \ge 0$. Then for every
natural number $k \ge 1$,
$$Q_{k-1} Q_{k+1} = Q_k^2 + 2(-1)^{k-1}.$$

Source: aBa Mbirika, Janee Schrader, and Jürgen Spilker, "Pell and Associated
Pell Braid Sequences as GCDs of Sums of k Consecutive Pell, Balancing, and
Related Numbers," Journal of Integer Sequences 26 (2023), Article 23.6.4,
Lemma [Cassini's identity for Q] (label lem:Cassini_identity_Qell_version).
Proves `Wanted` entry `associated_pell_cassini_identity`. -/
theorem associated_pell_cassini_identity
    (Q : ℕ → ℤ)
    (hQ_zero : Q 0 = 1)
    (hQ_one : Q 1 = 1)
    (hQ_rec : ∀ n : ℕ, Q (n + 2) = 2 * Q (n + 1) + Q n)
    (k : ℕ)
    (hk : 1 ≤ k) :
    Q (k - 1) * Q (k + 1) =
      Q k ^ 2 + 2 * (-1 : ℤ) ^ (k - 1) := by
  have r0 : Q 2 = 2 * Q 1 + Q 0 := hQ_rec 0
  have base : Q 0 * Q 2 - Q 1 ^ 2 = 2 * (-1 : ℤ) ^ 0 := by
    rw [hQ_zero, hQ_one, r0, hQ_zero, hQ_one]
    norm_num
  have step : ∀ j, Q (j + 1) * Q (j + 3) - Q (j + 2) ^ 2 =
      -(Q j * Q (j + 2) - Q (j + 1) ^ 2) := by
    intro j
    have r1 := hQ_rec j
    have r2 := hQ_rec (j + 1)
    have e1 : j + 1 + 2 = j + 3 := by omega
    have e2 : j + 1 + 1 = j + 2 := by omega
    rw [e1, e2] at r2
    linear_combination (Q (j + 1)) * r2 - (Q (j + 2)) * r1
  have E : ∀ j, Q j * Q (j + 2) - Q (j + 1) ^ 2 = 2 * (-1 : ℤ) ^ j := by
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
      ring
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have e0 : 1 + m = m + 1 := by omega
  have e1 : 1 + m - 1 = m := by omega
  have e2 : 1 + m + 1 = m + 2 := by omega
  rw [e1, e2, e0]
  have hE := E m
  linear_combination hE

end MetaMathlibExt
