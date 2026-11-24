/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LucasSequence
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Insert
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Composite unit shifts of Lucas sequences with $Q = 1$

For $P \ge 3$, every term of $U(P, 1)$ from index four onward is composite, as are its two unit
shifts. The proof factors each of the three values using the addition formula and Cassini's
identity.
-/

namespace MetaMathlibExt

namespace lucasU_q_one_shifts_eventually_composite

private abbrev u (P : ℤ) := lucasU ⟨P, 1, by decide⟩

private theorem u_add_two (P : ℤ) (n : ℕ) :
    u P (n + 2) = P * u P (n + 1) - u P n := by
  simp [u, lucasU_add_two]

private theorem u_cassini (P : ℤ) (n : ℕ) :
    u P (n + 1) ^ 2 - u P n * u P (n + 2) = 1 := by
  simpa using lucasU_cassini ⟨P, 1, by decide⟩ n

private theorem u_add (P : ℤ) (m n : ℕ) :
    u P (m + n + 1) = u P (m + 1) * u P (n + 1) - u P m * u P n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [u, lucasU]
  | one =>
    rw [show m + 1 + 1 = m + 2 by omega, u_add_two]
    simp [u, lucasU, mul_comm]
  | more n ih₀ ih₁ =>
    rw [show m + (n + 2) + 1 = (m + n + 1) + 2 by omega, u_add_two,
      show m + n + 1 + 1 = m + (n + 1) + 1 by omega, ih₁, ih₀,
      show n + 2 + 1 = (n + 1) + 2 by omega, u_add_two P (n + 1), u_add_two P n]
    ring

private theorem u_bounds {P : ℤ} (hP : 3 ≤ P) (k : ℕ) :
    1 ≤ u P (k + 1) ∧ 1 < u P (k + 2) - u P (k + 1) := by
  induction k with
  | zero =>
    change 1 ≤ (1 : ℤ) ∧ 1 < u P 2 - 1
    simpa [u, lucasU] using (show 1 < P - 1 by omega)
  | succ k ih =>
    have h : 0 ≤ (P - 2) * u P (k + 2) :=
      mul_nonneg (by omega) (by linarith [ih.1, ih.2])
    constructor
    · linarith [ih.1, ih.2]
    · rw [u_add_two P (k + 1)]
      linarith [ih.2]

private theorem composite_of_mul {m a b : ℤ} (h : m = a * b)
    (ha : 1 < a) (hb : 1 < b) : 1 < m ∧ ¬ m.natAbs.Prime := by
  rw [h, Int.natAbs_mul]
  exact ⟨by nlinarith, Nat.not_prime_mul (by omega) (by omega)⟩

private theorem even_composite {P : ℤ} (hP : 3 ≤ P) (k : ℕ) {d : ℤ}
    (hd : d ∈ ({-1, 0, 1} : Set ℤ)) :
    1 < u P (2 * (k + 2)) + d ∧ ¬ (u P (2 * (k + 2)) + d).natAbs.Prime := by
  have hU : u P (2 * (k + 2)) = u P (k + 2) * (u P (k + 3) - u P (k + 1)) := by
    rw [show 2 * (k + 2) = (k + 2) + (k + 1) + 1 by omega, u_add]
    ring
  have hC := u_cassini P (k + 1)
  obtain ⟨h₁, h₂⟩ := u_bounds hP k
  have h₃ : 1 < u P (k + 3) - u P (k + 2) := (u_bounds hP (k + 1)).2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl
  · refine composite_of_mul (a := u P (k + 2) + u P (k + 1))
      (b := u P (k + 3) - u P (k + 2)) ?_ (by omega) h₃
    linear_combination hU + hC
  · exact composite_of_mul (by simpa only [add_zero] using hU) (by omega) (by omega)
  · refine composite_of_mul (a := u P (k + 2) - u P (k + 1))
      (b := u P (k + 3) + u P (k + 2)) ?_ h₂ (by omega)
    linear_combination hU - hC

private theorem odd_composite {P : ℤ} (hP : 3 ≤ P) (k : ℕ) {d : ℤ}
    (hd : d ∈ ({-1, 0, 1} : Set ℤ)) :
    1 < u P (2 * (k + 2) + 1) + d ∧ ¬ (u P (2 * (k + 2) + 1) + d).natAbs.Prime := by
  have hU : u P (2 * (k + 2) + 1) = u P (k + 3) ^ 2 - u P (k + 2) ^ 2 := by
    rw [show 2 * (k + 2) + 1 = (k + 2) + (k + 2) + 1 by omega, u_add]
    ring
  obtain ⟨h₁, h₂⟩ := u_bounds hP k
  have h₃ : 1 < u P (k + 3) - u P (k + 2) := (u_bounds hP (k + 1)).2
  have h₄ : 1 < u P (k + 4) - u P (k + 3) := (u_bounds hP (k + 2)).2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  rcases hd with rfl | rfl | rfl
  · refine composite_of_mul (a := u P (k + 2)) (b := u P (k + 4) - u P (k + 2))
      ?_ (by omega) (by omega)
    linear_combination hU + u_cassini P (k + 2)
  · refine composite_of_mul (a := u P (k + 3) - u P (k + 2))
      (b := u P (k + 3) + u P (k + 2)) ?_ h₃ (by omega)
    linear_combination hU
  · refine composite_of_mul (a := u P (k + 3)) (b := u P (k + 3) - u P (k + 1))
      ?_ (by omega) (by omega)
    linear_combination hU - u_cassini P (k + 1)

end lucasU_q_one_shifts_eventually_composite

set_option backward.proofsInPublic true in
/-- **Unit shifts of $U_n(P, 1)$ are eventually composite.** Let $P \ge 3$ be an integer and
let $U_n = U_n(P, 1)$ be the Lucas sequence with $U_0 = 0$, $U_1 = 1$ and
$U_{n+2} = PU_{n+1} - U_n$. Then there is a natural number $N$ such that for every $n \ge N$
the three integers $U_n - 1$, $U_n$ and $U_n + 1$ are all composite, that is, each is
greater than $1$ and not prime.

Source: Dan Ismailescu, Daniel Hyunwoo Jeon, Aaron Kim, Joonbeom Kwon and Austin Lee,
*Shifting Lucas Sequences Away from Primes*, INTEGERS 25 (2025), Article A42, Theorem 2
(`integers-2025-A42-thm-2`). -/
public theorem lucasU_q_one_shifts_eventually_composite {P : ℤ} (hP : 3 ≤ P) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ d ∈ ({-1, 0, 1} : Set ℤ),
      1 < lucasU ⟨P, 1, by decide⟩ n + d ∧ ¬ (lucasU ⟨P, 1, by decide⟩ n + d).natAbs.Prime := by
  refine ⟨4, fun n hn d hd => ?_⟩
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (n - 4)
  · rw [show n = 2 * (k + 2) by omega]
    exact lucasU_q_one_shifts_eventually_composite.even_composite hP k hd
  · rw [show n = 2 * (k + 2) + 1 by omega]
    exact lucasU_q_one_shifts_eventually_composite.odd_composite hP k hd

end MetaMathlibExt
