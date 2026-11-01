/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modifications copyright (c) Meta Platforms, Inc. and affiliates.
Licensed under the license found in the LICENSE file in the root directory.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weighted pairs with shared endpoints

Nonnegative symmetric matrix weights with row sums at most `P` give incident weight at most
`4 * P`. A kernel supported on incident pairs, bounded above by `m ≥ 0`, then gives a quadratic
bound `4 * P * totalWeight * m`. Kernel values may be negative and nonsymmetric.
-/

@[expose] public section

namespace Matrix

open Finset

variable {ι R : Type*} [Fintype ι] [DecidableEq ι]
  [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

private lemma incident_indicator_le (x : R) (hx : 0 ≤ x) (A B C D : Prop)
    [Decidable A] [Decidable B] [Decidable C] [Decidable D] :
    (if A ∨ B ∨ C ∨ D then x else 0) ≤
      (if A then x else 0) + (if B then x else 0) +
        (if C then x else 0) + (if D then x else 0) := by
  split_ifs <;>
    simp_all only [add_zero, zero_add, le_refl, le_add_iff_nonneg_left,
      or_true, or_false, not_true_eq_false,
      not_false_eq_true]
  all_goals positivity

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma sum_first_endpoint (c : Matrix ι ι R) (v : ι) :
    (∑ q : ι × ι, if q.1 = v then c q.1 q.2 else 0) = ∑ b, c v b := by
  rw [Fintype.sum_prod_type]
  simp

omit [LinearOrder R] [IsStrictOrderedRing R] in
private lemma sum_second_endpoint (c : Matrix ι ι R) (v : ι) :
    (∑ q : ι × ι, if q.2 = v then c q.1 q.2 else 0) = ∑ a, c a v := by
  rw [Fintype.sum_prod_type]
  simp

/-- Pairs sharing an endpoint with a fixed pair have total weight at most `4 * P`.
Loops are permitted. Symmetry bounds the two column fibers by the same row bound. -/
theorem sum_weights_shared_endpoint_le (c : Matrix ι ι R) (P : R)
    (hc : ∀ a b, 0 ≤ c a b) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b, c a b ≤ P) (p : ι × ι) :
    (∑ q ∈ (univ.filter fun q : ι × ι =>
      q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2), c q.1 q.2) ≤ 4 * P := by
  rw [sum_filter]
  calc
    _ ≤ ∑ q : ι × ι,
        ((if q.1 = p.1 then c q.1 q.2 else 0) +
          (if q.1 = p.2 then c q.1 q.2 else 0) +
          (if q.2 = p.1 then c q.1 q.2 else 0) +
          (if q.2 = p.2 then c q.1 q.2 else 0)) :=
      sum_le_sum fun q _ => incident_indicator_le _ (hc _ _) _ _ _ _
    _ = (∑ b, c p.1 b) + (∑ b, c p.2 b) +
        (∑ a, c a p.1) + (∑ a, c a p.2) := by
      simp only [sum_add_distrib, sum_first_endpoint, sum_second_endpoint]
    _ ≤ P + P + P + P := by
      have hcol (v : ι) : ∑ a, c a v ≤ P := by
        simpa only [hs] using hP v
      exact add_le_add (add_le_add (add_le_add (hP _) (hP _)) (hcol _)) (hcol _)
    _ = 4 * P := by ring

omit [DecidableEq ι] in
private lemma sum_kernel_row_le (c : Matrix ι ι R) (P : R)
    (hc : ∀ a b, 0 ≤ c a b) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b, c a b ≤ P) (κ : Matrix (ι × ι) (ι × ι) R)
    (m : R) (hm : 0 ≤ m) (h1 : ∀ p q, κ p q ≤ m)
    (h0 : ∀ p q, q.1 ≠ p.1 → q.1 ≠ p.2 → q.2 ≠ p.1 → q.2 ≠ p.2 → κ p q = 0)
    (p : ι × ι) :
    (∑ q : ι × ι, c p.1 p.2 * c q.1 q.2 * κ p q) ≤ c p.1 p.2 * (4 * P * m) := by
  classical
  let S := univ.filter fun q : ι × ι =>
    q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2
  have hsplit : (∑ q : ι × ι, c p.1 p.2 * c q.1 q.2 * κ p q) =
      ∑ q ∈ S, c p.1 p.2 * c q.1 q.2 * κ p q := by
    rw [sum_filter]
    refine sum_congr rfl fun q _ => ?_
    by_cases h : q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      simp only [not_or] at h
      rw [h0 p q h.1 h.2.1 h.2.2.1 h.2.2.2, mul_zero]
  rw [hsplit]
  calc
    _ ≤ ∑ q ∈ S, c p.1 p.2 * c q.1 q.2 * m :=
      sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (h1 p q) (mul_nonneg (hc _ _) (hc _ _))
    _ = c p.1 p.2 * ((∑ q ∈ S, c q.1 q.2) * m) := by
      rw [sum_mul, mul_sum]
      simp only [mul_assoc]
    _ ≤ c p.1 p.2 * (4 * P * m) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (sum_weights_shared_endpoint_le c P hc hs hP p) hm)
        (hc _ _)

set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
/-- A kernel vanishing on pairs with no common endpoint has weighted quadratic sum at most
`4 * P * totalWeight * m`. Neither nonnegativity nor symmetry of the kernel is required;
diagonal weights are permitted, and no separate nonnegativity assumption on `P` is needed. -/
theorem sum_mul_mul_kernel_le (c : Matrix ι ι R) (P : R)
    (hc : ∀ a b, 0 ≤ c a b) (hs : ∀ a b, c a b = c b a)
    (hP : ∀ a, ∑ b, c a b ≤ P) (κ : Matrix (ι × ι) (ι × ι) R)
    (m : R) (hm : 0 ≤ m) (h1 : ∀ p q, κ p q ≤ m)
    (h0 : ∀ p q, q.1 ≠ p.1 → q.1 ≠ p.2 → q.2 ≠ p.1 → q.2 ≠ p.2 → κ p q = 0) :
    (∑ p : ι × ι, ∑ q : ι × ι, c p.1 p.2 * c q.1 q.2 * κ p q) ≤
      4 * P * (∑ a, ∑ b, c a b) * m := by
  calc
    _ ≤ ∑ p : ι × ι, c p.1 p.2 * (4 * P * m) :=
      sum_le_sum fun p _ => sum_kernel_row_le c P hc hs hP κ m hm h1 h0 p
    _ = 4 * P * (∑ a, ∑ b, c a b) * m := by
      rw [← sum_mul, Fintype.sum_prod_type]
      ring

private def offDiagonalWeights {g : ℕ} (c : Matrix (Fin g) (Fin g) ℕ) :
    Matrix (Fin g) (Fin g) ℤ := fun a b => if a = b then 0 else (c a b : ℤ)

private lemma sum_offDiagonalWeights {g : ℕ} (c : Matrix (Fin g) (Fin g) ℕ) (a : Fin g) :
    (∑ b, offDiagonalWeights c a b) = ((∑ b ∈ univ.erase a, c a b : ℕ) : ℤ) := by
  rw [Nat.cast_sum]
  rw [← sum_erase_add univ (fun b => offDiagonalWeights c a b) (mem_univ a)]
  simp only [offDiagonalWeights, ite_true, add_zero]
  refine sum_congr rfl fun b hb => ?_
  rw [ite_eq_right (Ne.symm (mem_erase.mp hb).1)]

private def orderedKernel {g : ℕ}
    (κ : Matrix (Fin g × Fin g) (Fin g × Fin g) ℤ) :
    Matrix (Fin g × Fin g) (Fin g × Fin g) ℤ := fun p q =>
  if p.1 ≠ p.2 ∧ q.1 ≠ q.2 then κ p q else 0

private lemma sum_orderedKernel {g : ℕ} (c : Matrix (Fin g) (Fin g) ℕ)
    (κ : Matrix (Fin g × Fin g) (Fin g × Fin g) ℤ) :
    (∑ p : Fin g × Fin g, ∑ q : Fin g × Fin g,
      offDiagonalWeights c p.1 p.2 * offDiagonalWeights c q.1 q.2 * orderedKernel κ p q) =
      ∑ p ∈ (univ.filter fun p : Fin g × Fin g => p.1 ≠ p.2),
        ∑ q ∈ (univ.filter fun q : Fin g × Fin g => q.1 ≠ q.2),
          (c p.1 p.2 : ℤ) * (c q.1 q.2 : ℤ) * κ p q := by
  rw [sum_filter]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : p.1 ≠ p.2
  · rw [ite_eq_left hp, sum_filter]
    refine sum_congr rfl fun q _ => ?_
    by_cases hq : q.1 ≠ q.2
    · rw [orderedKernel, ite_eq_left ⟨hp, hq⟩, ite_eq_left hq]
      simp only [offDiagonalWeights, ite_eq_right hp, ite_eq_right hq]
    · rw [orderedKernel, ite_eq_right (fun h => hq h.2), ite_eq_right hq, mul_zero]
  · rw [ite_eq_right hp]
    refine sum_eq_zero fun q _ => ?_
    rw [orderedKernel, ite_eq_right (fun h => hp h.1), mul_zero]

/-- The exact `Variance.StHence` estimate: natural weights on `Fin g`, integer kernel,
row sums over erased diagonals, and all directed distinct pairs. Diagonal weights are arbitrary.
The four inequalities in `h0` are precisely the negation of the source `Meets` disjunction.
The proof zeroes diagonal weights and masks the kernel outside the distinct-pair domain;
it does not extend a signed sum by adding unmasked terms. -/
theorem sum_ordered_nat_int_kernel_le (g P : ℕ) (c : Matrix (Fin g) (Fin g) ℕ)
    (hs : ∀ a b, c a b = c b a) (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P)
    (κ : Matrix (Fin g × Fin g) (Fin g × Fin g) ℤ) (m : ℤ) (hm : 0 ≤ m)
    (h0 : ∀ p ∈ (univ.filter fun p : Fin g × Fin g => p.1 ≠ p.2),
      ∀ q ∈ (univ.filter fun q : Fin g × Fin g => q.1 ≠ q.2),
        q.1 ≠ p.1 → q.1 ≠ p.2 → q.2 ≠ p.1 → q.2 ≠ p.2 → κ p q = 0)
    (h1 : ∀ p q, κ p q ≤ m) :
    (∑ p ∈ (univ.filter fun p : Fin g × Fin g => p.1 ≠ p.2),
      ∑ q ∈ (univ.filter fun q : Fin g × Fin g => q.1 ≠ q.2),
        (c p.1 p.2 : ℤ) * (c q.1 q.2 : ℤ) * κ p q) ≤
      ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) : ℕ) : ℤ) * m := by
  have hd : ∀ a b, 0 ≤ offDiagonalWeights c a b := by
    intro a b
    unfold offDiagonalWeights
    split_ifs <;> positivity
  have hds : ∀ a b, offDiagonalWeights c a b = offDiagonalWeights c b a := by
    intro a b
    simp only [offDiagonalWeights, hs a b, eq_comm]
  have hdP : ∀ a, ∑ b, offDiagonalWeights c a b ≤ (P : ℤ) := by
    intro a
    rw [sum_offDiagonalWeights]
    exact Int.ofNat_le.mpr (hP a)
  have hk1 : ∀ p q, orderedKernel κ p q ≤ m := by
    intro p q
    unfold orderedKernel
    split_ifs
    · exact h1 p q
    · exact hm
  have hk0 : ∀ p q, q.1 ≠ p.1 → q.1 ≠ p.2 → q.2 ≠ p.1 → q.2 ≠ p.2 →
      orderedKernel κ p q = 0 := by
    intro p q h₁ h₂ h₃ h₄
    unfold orderedKernel
    split_ifs with h
    · exact h0 p (mem_filter.mpr ⟨mem_univ _, h.1⟩)
        q (mem_filter.mpr ⟨mem_univ _, h.2⟩) h₁ h₂ h₃ h₄
    · rfl
  have H := sum_mul_mul_kernel_le (offDiagonalWeights c) (P : ℤ)
    hd hds hdP (orderedKernel κ) m hm hk1 hk0
  rw [sum_orderedKernel] at H
  simpa only [sum_offDiagonalWeights, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using H

end Matrix
