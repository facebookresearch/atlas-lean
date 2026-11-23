/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modifications copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/

module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.NormNum

/-!
# Finite parity products modulo powers of two

The finite expansion of a product of even-cardinality indicators and parity signs can be
cut off at total degree `M` modulo `2 ^ ν` when `ν - 1 + #J₁ ≤ M`. Each even-indicator
coefficient loses at most one power of two, which accounts for the shift by `#J₁`.

Adapted from `ClauseBound.ParityChecks.StepOne.cutoff_one` in
`anthropics/formal-math`, commit `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`,
`proof/rates/ClauseBound/ParityChecks/StepOne.lean`.
-/

@[expose] public section

namespace ParityProduct

open Finset

/-- The integer indicator that a natural number is even. -/
def evenIndicator (q : ℕ) : ℤ := if Even q then 1 else 0

/-- The coefficients of the even-indicator expansion: one at zero and
`(-1) ^ i * 2 ^ (i - 1)` at positive indices. -/
def parityCoeff (i : ℕ) : ℤ := if i = 0 then 1 else (-1) ^ i * 2 ^ (i - 1)

/-- Twice the parity coefficient is the sign coefficient, with a correction at zero. -/
theorem two_mul_parityCoeff (i : ℕ) :
    2 * parityCoeff i = (-2) ^ i + if i = 0 then 1 else 0 := by
  unfold parityCoeff
  cases i with
  | zero => simp
  | succ k =>
    rw [ite_eq_right (Nat.succ_ne_zero k), ite_eq_right (Nat.succ_ne_zero k),
      Nat.add_sub_cancel, show (-2 : ℤ) = -1 * 2 by norm_num, mul_pow,
      pow_succ (2 : ℤ) k]
    simp [mul_assoc, mul_comm]

/-- Twice the even indicator is one plus the parity sign. -/
theorem two_mul_evenIndicator (q : ℕ) : 2 * evenIndicator q = 1 + (-1) ^ q := by
  unfold evenIndicator
  by_cases h : Even q
  · rw [ite_eq_left h, h.neg_one_pow]
    norm_num
  · rw [ite_eq_right h, (Nat.not_even_iff_odd.1 h).neg_one_pow]
    norm_num

private theorem sum_powerset_neg_two {E : Type*} (A : Finset E) :
    ∑ s ∈ A.powerset, (-2 : ℤ) ^ #s = (-1) ^ #A := by
  simpa using sum_pow_mul_eq_add_pow (-2 : ℤ) 1 A

/-- Summing parity coefficients over all subsets gives the even-cardinality indicator. -/
theorem sum_powerset_parityCoeff {E : Type*} (A : Finset E) :
    ∑ s ∈ A.powerset, parityCoeff #s = evenIndicator #A := by
  classical
  have hz : ∑ s ∈ A.powerset, (if #s = 0 then (1 : ℤ) else 0) = 1 := by
    simp
  have h : 2 * ∑ s ∈ A.powerset, parityCoeff #s = 2 * evenIndicator #A := by
    rw [two_mul_evenIndicator, mul_sum]
    simp_rw [two_mul_parityCoeff]
    rw [sum_add_distrib, sum_powerset_neg_two, hz]
    exact add_comm _ _
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h

variable {E : Type*} {r : ℕ}

private def factor (J₁ J₂ : Finset (Fin r)) (j : Fin r) (s : Finset E) : ℤ :=
  if j ∈ J₁ then parityCoeff #s else if j ∈ J₂ then (-2) ^ #s else 1

private def domain (A : Fin r → Finset E) (J : Finset (Fin r)) (j : Fin r) :
    Finset (Finset E) :=
  if j ∈ J then (A j).powerset else {∅}

private theorem prod_mul_prod {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂)
    (a b : Fin r → ℤ) :
    (∏ j ∈ J₁, a j) * ∏ j ∈ J₂, b j =
      ∏ j, if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1 := by
  have h : ∀ j : Fin r, (if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1) =
      (if j ∈ J₁ then a j else 1) * if j ∈ J₂ then b j else 1 := by
    intro j
    by_cases h1 : j ∈ J₁
    · rw [ite_eq_left h1, ite_eq_left h1,
        ite_eq_right (disjoint_left.1 hJ h1), mul_one]
    · rw [ite_eq_right h1, ite_eq_right h1, one_mul]
  simp only [h]
  rw [prod_mul_distrib, prod_ite_mem, prod_ite_mem, univ_inter, univ_inter]

private theorem sum_all {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂)
    (A : Fin r → Finset E) :
    ∑ S ∈ Fintype.piFinset (domain A (J₁ ∪ J₂)), ∏ j, factor J₁ J₂ j (S j) =
      (∏ j ∈ J₁, evenIndicator #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) := by
  rw [← prod_univ_sum, prod_mul_prod hJ]
  refine prod_congr rfl fun j _ => ?_
  unfold domain factor
  by_cases h1 : j ∈ J₁
  · simp only [ite_eq_left h1, ite_eq_left (mem_union_left J₂ h1)]
    exact sum_powerset_parityCoeff _
  · by_cases h2 : j ∈ J₂
    · simp only [ite_eq_right h1, ite_eq_left h2, ite_eq_left (mem_union_right J₁ h2)]
      exact sum_powerset_neg_two _
    · have h3 : j ∉ J₁ ∪ J₂ := fun h => (mem_union.1 h).elim h1 h2
      simp only [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, sum_singleton]

private theorem two_pow_dvd_parityCoeff (i : ℕ) : (2 : ℤ) ^ (i - 1) ∣ parityCoeff i := by
  unfold parityCoeff
  split_ifs with h
  · rw [h]
    exact one_dvd _
  · exact Dvd.intro_left _ rfl

private theorem two_pow_dvd_neg_two_pow (i : ℕ) : (2 : ℤ) ^ i ∣ (-2) ^ i := by
  rw [show (-2 : ℤ) = -1 * 2 by norm_num, mul_pow]
  exact Dvd.intro_left _ rfl

private theorem dvd_factor {J₁ J₂ : Finset (Fin r)} (A : Fin r → Finset E)
    {S : Fin r → Finset E} (hS : S ∈ Fintype.piFinset (domain A (J₁ ∪ J₂)))
    (j : Fin r) :
    (2 : ℤ) ^ (#(S j) - if j ∈ J₁ then 1 else 0) ∣ factor J₁ J₂ j (S j) := by
  unfold factor
  by_cases h1 : j ∈ J₁
  · simp only [ite_eq_left h1]
    exact two_pow_dvd_parityCoeff _
  · by_cases h2 : j ∈ J₂
    · simp only [ite_eq_right h1, ite_eq_left h2, Nat.sub_zero]
      exact two_pow_dvd_neg_two_pow _
    · have h3 : j ∉ J₁ ∪ J₂ := fun h => (mem_union.1 h).elim h1 h2
      have h4 := Fintype.mem_piFinset.1 hS j
      rw [domain, ite_eq_right h3, mem_singleton] at h4
      simp only [ite_eq_right h1, ite_eq_right h2, h4, card_empty, Nat.sub_zero, pow_zero]
      exact one_dvd _

private theorem dvd_term {J₁ J₂ : Finset (Fin r)} (A : Fin r → Finset E)
    {S : Fin r → Finset E} (hS : S ∈ Fintype.piFinset (domain A (J₁ ∪ J₂))) {ν : ℕ}
    (hν : ν + #J₁ ≤ ∑ j, #(S j)) : (2 : ℤ) ^ ν ∣ ∏ j, factor J₁ J₂ j (S j) := by
  have h2 : ∑ j, #(S j) ≤ ∑ j : Fin r, (#(S j) - if j ∈ J₁ then 1 else 0) + #J₁ := by
    have h3 : #J₁ = ∑ j : Fin r, if j ∈ J₁ then 1 else 0 := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter, Nat.cast_id]
    rw [h3, ← sum_add_distrib]
    exact sum_le_sum fun j _ => by omega
  refine (pow_dvd_pow 2
    (by omega : ν ≤ ∑ j : Fin r, (#(S j) - if j ∈ J₁ then 1 else 0))).trans ?_
  rw [← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun j _ => dvd_factor A hS j

/-- A product of even-cardinality indicators and parity signs is congruent to its finite
subset expansion cut off at total degree `M`. Each even-indicator factor costs at most one
power of two, so the cutoff must satisfy `ν - 1 + #J₁ ≤ M`, with `1 ≤ ν`.
Indices outside `J₁ ∪ J₂` select only the empty subset. -/
theorem prod_evenIndicator_mul_prod_neg_one_pow_modEq {J₁ J₂ : Finset (Fin r)}
    (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) {ν M : ℕ} (hν : 1 ≤ ν)
    (hM : ν - 1 + #J₁ ≤ M) :
    (∏ j ∈ J₁, evenIndicator #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) ≡
      ∑ S ∈ (Fintype.piFinset fun j : Fin r =>
        if j ∈ J₁ ∪ J₂ then (A j).powerset else {∅}).filter (fun S => ∑ j, #(S j) ≤ M),
        (∏ j ∈ J₁, parityCoeff #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j)
      [ZMOD 2 ^ ν] := by
  classical
  have hterm : ∀ S : Fin r → Finset E,
      (∏ j ∈ J₁, parityCoeff #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j) =
        ∏ j, factor J₁ J₂ j (S j) := fun S => prod_mul_prod hJ _ _
  have hcut :
      (∏ j ∈ J₁, evenIndicator #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) ≡
      ∑ S ∈ (Fintype.piFinset (domain A (J₁ ∪ J₂))).filter
        (fun S => ∑ j, #(S j) ≤ M), ∏ j, factor J₁ J₂ j (S j) [ZMOD 2 ^ ν] := by
    rw [← sum_all hJ A, sum_filter]
    apply Int.ModEq.sum
    intro S hS
    by_cases h : ∑ j, #(S j) ≤ M
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact Int.modEq_zero_iff_dvd.2 (dvd_term A hS (by omega))
  unfold domain at hcut
  simpa only [← hterm] using hcut

end ParityProduct
