/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The two exact-source consumers adapt the statements and composition proof
from Fermat's Last Theorem in Lean 4, revision
6e837e75355538c7f80bab5b956861e86c4eacc2, in these four files:
Theorems/Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line.lean
P2M/Sol/S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_eq_of_shellRecurrent_finsum_line.lean
Theorems/Thm_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence.lean
P2M/Sol/S_Polynomial_exists_polynomial_forall_tsum_mul_zpow_mul_eval_eq_zpow_mul_eval_of_separatedRational_of_shellRecurrence.lean
Copyright 2026 Anthropic, PBC; licensed under Apache-2.0.
No individual source author is named. The source NOTICE credits Mathlib
and its respective authors. The application and boundary proofs below
are new and use only the inherited public recurrence and resummation APIs.
-/
module

public import MathlibExt.Analysis.SpecificLimits.LaurentRecurrence
public import MathlibExt.LinearAlgebra.LinearRecurrence.WeightedLine
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.ComputeDegree

open scoped BigOperators
open Polynomial

@[expose] public section

noncomputable section

namespace LaurentRecurrenceTest

/-- The literal source shape, with no replacement convergence premise. -/
theorem source_laurent
    (w : ℤ × ℤ → ℂ) (N₁ : ℤ)
    (hw : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → w n = 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hc : ∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N → (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
        if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0) m = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * (fun t : ℤ => ∑ᶠ n : ℤ × ℤ,
          if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = t then w n else 0)
          (N + (m : ℤ) - (i : ℤ)) = 0)) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ =>
          w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ,
          w n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X :=
  Polynomial.exists_laurent_of_recurrence_weighted_line
    w N₁ hw e₁ e₂ he₁ he₂ hc

/-- The second source is an importing composition, not a second recurrence. -/
theorem source_weighted_composite
    (A : ℤ × ℤ → ℂ) (b : ℤ → ℂ) (α β : ℂ) (hα : α ≠ 0) (hβ : β ≠ 0)
    (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hA : ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1),
          ∑ l ∈ Finset.range (D₂.natDegree + 1),
            D₁.coeff i * D₂.coeff l *
              A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0))
    (hb : ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M' : ℕ), E.eval 0 ≠ 0 ∧
      (∀ m : ℤ, m < N₂ → b m = 0) ∧
      (∀ m : ℕ, M' ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * b (N₂ + (m : ℤ) - (i : ℤ)) = 0)) :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 →
        Summable (fun n : ℤ × ℤ => A n * b n.1 * α ^ n.1 * β ^ n.2 *
          X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) →
        (∑' n : ℤ × ℤ, A n * b n.1 * α ^ n.1 * β ^ n.2 *
          X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X := by
  obtain ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ := hA
  have hc := Polynomial.exists_recurrence_weighted_line A b α β hα hβ
    e₁ e₂ he₁ he₂ ⟨N₁, D₁, D₂, M, hD₁, hD₂, hsupp, hrec⟩ hb
  apply Polynomial.exists_laurent_of_recurrence_weighted_line
    (fun n => A n * b n.1 * α ^ n.1 * β ^ n.2) N₁ _ e₁ e₂ he₁ he₂ hc
  intro n hn
  simp only [hsupp n hn, zero_mul]

/-- The supports -1 and -3 deliberately differ. -/
def quadrant (n : ℤ × ℤ) : ℂ :=
  if -1 ≤ n.1 ∧ -1 ≤ n.2 then 1 else 0

def ramp (i : ℤ) : ℂ := if -3 ≤ i then ((i + 4 : ℤ) : ℂ) else 0

def weighted (n : ℤ × ℤ) : ℂ :=
  quadrant n * ramp n.1 * (2 : ℂ) ^ n.1 * (3 : ℂ) ^ n.2

private theorem degree_difference :
    (1 - Polynomial.X : Polynomial ℂ).natDegree = 1 := by
  compute_degree
  norm_num

private theorem degree_square_difference :
    ((1 - Polynomial.X : Polynomial ℂ) ^ 2).natDegree = 2 := by
  compute_degree
  norm_num

theorem quadrant_support (n : ℤ × ℤ) (hn : n.1 < -1 ∨ n.2 < -1) :
    quadrant n = 0 := by
  simp only [quadrant]
  split_ifs <;> first | omega | rfl

theorem quadrant_recurrence (m₁ m₂ : ℕ) (hm : 1 ≤ m₁ ∨ 1 ≤ m₂) :
    ∑ i ∈ Finset.range ((1 - Polynomial.X : Polynomial ℂ).natDegree + 1),
      ∑ l ∈ Finset.range ((1 - Polynomial.X : Polynomial ℂ).natDegree + 1),
        (1 - Polynomial.X : Polynomial ℂ).coeff i *
          (1 - Polynomial.X : Polynomial ℂ).coeff l *
          quadrant (-1 + (m₁ : ℤ) - (i : ℤ), -1 + (m₂ : ℤ) - (l : ℤ)) = 0 := by
  rw [degree_difference]
  norm_num [Finset.sum_range_succ, coeff_sub, coeff_one, coeff_X, quadrant]
  split_ifs <;> norm_num at * <;> omega

theorem ramp_support (i : ℤ) (hi : i < -3) : ramp i = 0 := by
  simp [ramp, show ¬ -3 ≤ i by omega]

theorem ramp_recurrence (m : ℕ) (hm : 2 ≤ m) :
    ∑ i ∈ Finset.range (((1 - Polynomial.X : Polynomial ℂ) ^ 2).natDegree + 1),
      ((1 - Polynomial.X : Polynomial ℂ) ^ 2).coeff i *
        ramp (-3 + (m : ℤ) - (i : ℤ)) = 0 := by
  have hsquare : (1 - Polynomial.X : Polynomial ℂ) ^ 2 =
      1 - C 2 * Polynomial.X + Polynomial.X ^ 2 := by
    rw [show C (2 : ℂ) = 2 from map_ofNat C 2]
    ring
  rw [degree_square_difference]
  norm_num [hsquare, Finset.sum_range_succ,
    coeff_add, coeff_sub, coeff_C_mul, coeff_one, coeff_X, ramp]
  split_ifs
  all_goals first | omega | ring

theorem quadrant_hypotheses :
    ∃ (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ),
      D₁.eval 0 ≠ 0 ∧ D₂.eval 0 ≠ 0 ∧
      (∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → quadrant n = 0) ∧
      (∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
        ∑ i ∈ Finset.range (D₁.natDegree + 1),
          ∑ l ∈ Finset.range (D₂.natDegree + 1),
            D₁.coeff i * D₂.coeff l *
              quadrant (N₁ + (m₁ : ℤ) - (i : ℤ),
                N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) := by
  exact ⟨-1, 1 - Polynomial.X, 1 - Polynomial.X, 1,
    by simp, by simp, quadrant_support, quadrant_recurrence⟩

theorem ramp_hypotheses :
    ∃ (N₂ : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
      (∀ i : ℤ, i < N₂ → ramp i = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * ramp (N₂ + (m : ℤ) - (i : ℤ)) = 0) := by
  exact ⟨-3, (1 - Polynomial.X) ^ 2, 2,
    by simp, ramp_support, ramp_recurrence⟩

private theorem summable_norm_of_nat_of_zero_below (f : ℤ → ℂ) (K : ℕ)
    (hf : Summable (fun n : ℕ => ‖f n‖))
    (h0 : ∀ t : ℤ, t < -(K : ℤ) → f t = 0) :
    Summable (fun t : ℤ => ‖f t‖) := by
  apply hf.of_nat_of_neg_add_one
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.range K) ?_).summable
  intro n hn
  rw [h0 _ (by simp only [Finset.mem_range] at hn; omega), norm_zero]

private theorem summable_norm_linear (r : ℂ) (hr : ‖r‖ < 1) :
    Summable (fun i : ℤ =>
      ‖if -1 ≤ i then ((i + 4 : ℤ) : ℂ) * r ^ i else 0‖) := by
  apply summable_norm_of_nat_of_zero_below _ 1
  · have hp : Summable (fun n : ℕ => (n : ℝ) * ‖r‖ ^ n) := by
      simpa only [pow_one] using
        summable_pow_mul_geometric_of_norm_lt_one 1
          (show ‖(‖r‖ : ℝ)‖ < 1 by simpa using hr)
    have hg : Summable (fun n : ℕ => ‖r‖ ^ n) :=
      summable_geometric_of_lt_one (norm_nonneg r) hr
    refine (hp.add (hg.mul_left 4)).congr fun n => ?_
    have hc : ‖(((n : ℤ) + 4 : ℤ) : ℂ)‖ = (n : ℝ) + 4 := by
      rw [show (n : ℤ) + 4 = ((n + 4 : ℕ) : ℤ) by omega,
        Int.cast_natCast, Complex.norm_natCast, Nat.cast_add]
      norm_num
    rw [ite_eq_left (show (-1 : ℤ) ≤ n by omega), norm_mul,
      zpow_natCast, norm_pow, hc, add_mul]
  · intro t ht
    simp [show ¬ -1 ≤ t by omega]

private theorem summable_norm_geometric (r : ℂ) (hr : ‖r‖ < 1) :
    Summable (fun i : ℤ => ‖if -1 ≤ i then r ^ i else 0‖) := by
  apply summable_norm_of_nat_of_zero_below _ 1
  · refine (summable_norm_geometric_of_norm_lt_one hr).congr fun n => ?_
    simp [show (-1 : ℤ) ≤ n by omega]
  · intro t ht
    simp [show ¬ -1 ≤ t by omega]

theorem weighted_factorization (X : ℂ) (hX : X ≠ 0)
    (e₁ e₂ : ℕ) (n : ℤ × ℤ) :
    weighted n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2) =
      (if -1 ≤ n.1 then ((n.1 + 4 : ℤ) : ℂ) * (2 * X ^ e₁) ^ n.1 else 0) *
      (if -1 ≤ n.2 then (3 * X ^ e₂) ^ n.2 else 0) := by
  by_cases h1 : -1 ≤ n.1 <;> by_cases h2 : -1 ≤ n.2
  · have hb : -3 ≤ n.1 := by omega
    simp only [weighted, quadrant, ramp, h1, h2, hb, and_self, ite_true,
      one_mul, mul_zpow, zpow_add₀ hX, zpow_mul, zpow_natCast]
    ring
  all_goals simp [weighted, quadrant, h1, h2]

theorem weighted_norm_summable (X : ℂ) (hX : X ≠ 0) (e₁ e₂ : ℕ)
    (h1 : ‖2 * X ^ e₁‖ < 1) (h2 : ‖3 * X ^ e₂‖ < 1) :
    Summable (fun n : ℤ × ℤ =>
      ‖weighted n * X ^ ((e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2)‖) := by
  refine ((summable_norm_linear _ h1).mul_norm
    (summable_norm_geometric _ h2)).congr fun n => ?_
  exact congrArg norm (weighted_factorization X hX e₁ e₂ n).symm

theorem weighted_disk_nonempty :
    ∃ X : ℂ, 0 < ‖X‖ ∧ ‖X‖ < 1 / 6 := by
  exact ⟨1 / 12, by norm_num [norm_div]⟩

/-- One certificate works throughout the punctured disk, with summability. -/
theorem weighted_laurent_application :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, 0 < ‖X‖ → ‖X‖ < 1 / 6 →
        (∑' n : ℤ × ℤ, weighted n * X ^ (2 * n.1 + 3 * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X := by
  obtain ⟨P, Q, m₀, hQ, h⟩ := source_weighted_composite
    quadrant ramp 2 3 (by norm_num) (by norm_num) 2 3
    (by omega) (by omega) quadrant_hypotheses ramp_hypotheses
  refine ⟨P, Q, m₀, hQ, fun X hpos hx => ?_⟩
  have hX : X ≠ 0 := norm_pos_iff.mp hpos
  have h1 : ‖(2 : ℂ) * X ^ 2‖ < 1 := by
    calc
      ‖(2 : ℂ) * X ^ 2‖ = 2 * ‖X‖ ^ 2 := by norm_num [norm_mul, norm_pow]
      _ < 2 * (1 / 6 : ℝ) ^ 2 := by gcongr
      _ < 1 := by norm_num
  have h2 : ‖(3 : ℂ) * X ^ 3‖ < 1 := by
    calc
      ‖(3 : ℂ) * X ^ 3‖ = 3 * ‖X‖ ^ 3 := by norm_num [norm_mul, norm_pow]
      _ < 3 * (1 / 6 : ℝ) ^ 3 := by gcongr
      _ < 1 := by norm_num
  exact h X hX (weighted_norm_summable X hX 2 3 h1 h2).of_norm

/-- The lowest shell is nonzero even though its index is negative. -/
theorem weighted_first_shell (e₁ e₂ : ℕ) (he₁ : 0 < e₁) (he₂ : 0 < e₂) :
    (∑ᶠ n : ℤ × ℤ,
      if (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 = -(e₁ : ℤ) - (e₂ : ℤ)
      then weighted n else 0) = 1 / 2 := by
  classical
  have he1 : (0 : ℤ) < e₁ := by exact_mod_cast he₁
  have he2 : (0 : ℤ) < e₂ := by exact_mod_cast he₂
  calc
    _ = ∑ᶠ n : ℤ × ℤ, if n = (-1, -1) then (1 / 2 : ℂ) else 0 := by
      apply finsum_congr
      intro n
      by_cases hn : n = (-1, -1)
      · subst n
        norm_num [weighted, quadrant, ramp]
        ring_nf
      · by_cases h1 : -1 ≤ n.1 <;> by_cases h2 : -1 ≤ n.2
        · have hnot : (e₁ : ℤ) * n.1 + (e₂ : ℤ) * n.2 ≠
              -(e₁ : ℤ) - (e₂ : ℤ) := by
            intro heq
            have hp1 := mul_nonneg he1.le (show 0 ≤ n.1 + 1 by omega)
            have hp2 := mul_nonneg he2.le (show 0 ≤ n.2 + 1 by omega)
            have hz1 : (e₁ : ℤ) * (n.1 + 1) = 0 := by nlinarith
            have hz2 : (e₂ : ℤ) * (n.2 + 1) = 0 := by nlinarith
            have hc1 := (mul_eq_zero.mp hz1).resolve_left (ne_of_gt he1)
            have hc2 := (mul_eq_zero.mp hz2).resolve_left (ne_of_gt he2)
            exact hn (Prod.ext (by omega) (by omega))
          simp [hn, hnot]
        all_goals simp [hn, weighted, quadrant, h1, h2]
    _ = 1 / 2 := by
      rw [finsum_eq_single _ (-1, -1) (by intro n hn; simp [hn])]
      simp

theorem weighted_negative_first_shell :
    (∑ᶠ n : ℤ × ℤ, if 2 * n.1 + 3 * n.2 = -5 then weighted n else 0) =
      1 / 2 := by
  simpa using weighted_first_shell 2 3 (by omega) (by omega)

theorem noncoprime_odd_shells (k : ℤ) :
    (∑ᶠ n : ℤ × ℤ,
      if 2 * n.1 + 4 * n.2 = 2 * k + 1 then weighted n else 0) = 0 := by
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [ite_eq_right (by omega)]

theorem noncoprime_nonzero_even_shell :
    (∑ᶠ n : ℤ × ℤ, if 2 * n.1 + 4 * n.2 = -6 then weighted n else 0) ≠ 0 := by
  have h := weighted_first_shell 2 4 (by omega) (by omega)
  norm_num at h
  rw [h]
  norm_num

/-- An infinite geometric tail and two independent exceptional coefficients. -/
def exceptional (t : ℤ) : ℂ :=
  if t = -2 then 5 else if t = -1 then 7 else if 0 ≤ t then 2 ^ t else 0

def exceptionalAnnihilator : Polynomial ℂ := 1 - C 2 * Polynomial.X

theorem exceptional_support (t : ℤ) (ht : t < -2) : exceptional t = 0 := by
  simp [exceptional, show t ≠ -2 by omega, show t ≠ -1 by omega,
    show ¬ 0 ≤ t by omega]

theorem exceptional_nonnegative (t : ℤ) (ht : 0 ≤ t) :
    exceptional t = (2 : ℂ) ^ t := by
  simp [exceptional, show t ≠ -2 by omega, show t ≠ -1 by omega, ht]

private theorem degree_exceptional : exceptionalAnnihilator.natDegree = 1 := by
  unfold exceptionalAnnihilator
  compute_degree
  norm_num

theorem exceptional_convolution (t : ℤ) :
    (∑ i ∈ Finset.range (exceptionalAnnihilator.natDegree + 1),
      exceptionalAnnihilator.coeff i * exceptional (t - (i : ℤ))) =
        exceptional t - 2 * exceptional (t - 1) := by
  rw [degree_exceptional]
  norm_num [exceptionalAnnihilator, Finset.sum_range_succ,
    coeff_sub, coeff_C_mul, coeff_one, coeff_X]
  ring

theorem exceptional_recurrence (t : ℤ) (ht : 1 ≤ t) :
    (∑ i ∈ Finset.range (exceptionalAnnihilator.natDegree + 1),
      exceptionalAnnihilator.coeff i * exceptional (t - (i : ℤ))) = 0 := by
  rw [exceptional_convolution, exceptional_nonnegative _ (by omega),
    exceptional_nonnegative _ (by omega)]
  have hp : (2 : ℂ) ^ t = 2 * (2 : ℂ) ^ (t - 1) := by
    calc
      (2 : ℂ) ^ t = (2 : ℂ) ^ ((t - 1) + 1) := by congr 1; omega
      _ = (2 : ℂ) ^ (t - 1) * 2 := by
        rw [zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one]
      _ = 2 * (2 : ℂ) ^ (t - 1) := mul_comm _ _
  rw [hp, sub_self]

theorem exceptional_residual_polynomial :
    (∑ j ∈ Finset.range ((1 : ℤ) - (-2)).toNat,
      C (∑ i ∈ Finset.range (exceptionalAnnihilator.natDegree + 1),
        exceptionalAnnihilator.coeff i *
          exceptional (-2 + (j : ℤ) - (i : ℤ))) * Polynomial.X ^ j) =
      (5 - 3 * Polynomial.X - 13 * Polynomial.X ^ 2 : Polynomial ℂ) := by
  simp_rw [exceptional_convolution]
  norm_num [exceptional, Finset.sum_range_succ, map_ofNat]
  ring

theorem exceptional_norm_summable (X : ℂ) (hx : ‖X‖ < 1 / 2) :
    Summable (fun t : ℤ => ‖exceptional t * X ^ t‖) := by
  have hr : ‖(2 : ℂ) * X‖ < 1 := by
    norm_num [norm_mul]
    linarith
  apply summable_norm_of_nat_of_zero_below _ 2
  · refine (summable_norm_geometric_of_norm_lt_one hr).congr fun n => ?_
    rw [exceptional_nonnegative _ (by omega), zpow_natCast, zpow_natCast,
      mul_pow]
  · intro t ht
    rw [exceptional_support t ht, zero_mul]

theorem exceptional_disk_nonempty :
    ∃ X : ℂ, 0 < ‖X‖ ∧ ‖X‖ < 1 / 2 := by
  exact ⟨1 / 4, by norm_num [norm_div]⟩

/-- The explicit core fixes the numerator and shift, unlike an existential. -/
theorem exceptional_laurent_identity (X : ℂ) (hX : X ≠ 0)
    (hs : Summable (fun t : ℤ => exceptional t * X ^ t)) :
    (∑' t : ℤ, exceptional t * X ^ t) * (1 - 2 * X) =
      X ^ (-2 : ℤ) * (5 - 3 * X - 13 * X ^ 2) := by
  have h := Polynomial.tsum_mul_eval_eq_zpow_mul_eval_of_recurrence
    exceptional exceptionalAnnihilator (-2) 1 exceptional_support
    exceptional_recurrence X hX hs
  rw [exceptional_residual_polynomial] at h
  simpa [exceptionalAnnihilator] using h

theorem exceptional_laurent_application (X : ℂ)
    (hpos : 0 < ‖X‖) (hx : ‖X‖ < 1 / 2) :
    (∑' t : ℤ, exceptional t * X ^ t) * (1 - 2 * X) =
      X ^ (-2 : ℤ) * (5 - 3 * X - 13 * X ^ 2) :=
  exceptional_laurent_identity X (norm_pos_iff.mp hpos)
    (exceptional_norm_summable X hx).of_norm

/-- Axis embedding used for both infinite and finite-support examples. -/
def axis (f : ℤ → ℂ) (n : ℤ × ℤ) : ℂ := if n.2 = 0 then f n.1 else 0

theorem axis_shell (f : ℤ → ℂ) (t : ℤ) :
    (∑ᶠ n : ℤ × ℤ, if n.1 + n.2 = t then axis f n else 0) = f t := by
  classical
  rw [finsum_eq_single _ (t, 0)]
  · simp [axis]
  · intro n hn
    by_cases hj : n.2 = 0
    · have hi : n.1 ≠ t := fun hi => hn (Prod.ext hi hj)
      simp [hj, hi]
    · simp [axis, hj]

private theorem axis_factorization (f : ℤ → ℂ) (X : ℂ) (n : ℤ × ℤ) :
    axis f n * X ^ (n.1 + n.2) =
      (f n.1 * X ^ n.1) * (if n.2 = 0 then 1 else 0) := by
  by_cases hj : n.2 = 0 <;> simp [axis, hj]

private theorem norm_summable_delta_zero :
    Summable (fun j : ℤ => ‖if j = 0 then (1 : ℂ) else 0‖) := by
  refine (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable.congr fun j => ?_
  by_cases hj : j = 0 <;> simp [hj]

theorem axis_norm_summable (f : ℤ → ℂ) (X : ℂ)
    (hf : Summable (fun t : ℤ => ‖f t * X ^ t‖)) :
    Summable (fun n : ℤ × ℤ => ‖axis f n * X ^ (n.1 + n.2)‖) := by
  refine (hf.mul_norm norm_summable_delta_zero).congr fun n => ?_
  exact congrArg norm (axis_factorization f X n).symm

theorem axis_tsum (f : ℤ → ℂ) (X : ℂ)
    (hf : Summable (fun t : ℤ => ‖f t * X ^ t‖)) :
    (∑' n : ℤ × ℤ, axis f n * X ^ (n.1 + n.2)) =
      ∑' t : ℤ, f t * X ^ t := by
  calc
    _ = ∑' n : ℤ × ℤ,
        (f n.1 * X ^ n.1) * (if n.2 = 0 then 1 else 0) :=
      tsum_congr (axis_factorization f X)
    _ = (∑' t : ℤ, f t * X ^ t) *
        ∑' j : ℤ, (if j = 0 then (1 : ℂ) else 0) :=
      (tsum_mul_tsum_of_summable_norm hf norm_summable_delta_zero).symm
    _ = _ := by simp

theorem exceptional_axis_support (n : ℤ × ℤ)
    (hn : n.1 < -2 ∨ n.2 < -2) : axis exceptional n = 0 := by
  by_cases hj : n.2 = 0
  · have hi : n.1 < -2 := by omega
    simp [axis, hj, exceptional_support _ hi]
  · simp [axis, hj]

/-- Natural cutoff three is absolute cutoff one at lower index minus two. -/
theorem exceptional_axis_recurrence (m : ℕ) (hm : 3 ≤ m) :
    (∑ i ∈ Finset.range (exceptionalAnnihilator.natDegree + 1),
      exceptionalAnnihilator.coeff i *
        (∑ᶠ n : ℤ × ℤ, if n.1 + n.2 = -2 + (m : ℤ) - (i : ℤ)
          then axis exceptional n else 0)) = 0 := by
  simp_rw [axis_shell]
  exact exceptional_recurrence _ (by omega)

theorem exceptional_tail_nonzero (n : ℕ) : exceptional n ≠ 0 := by
  rw [exceptional_nonnegative _ (by omega)]
  exact zpow_ne_zero _ (by norm_num)

/-- The full source interface also handles the same infinite axis family. -/
theorem exceptional_axis_application :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, 0 < ‖X‖ → ‖X‖ < 1 / 2 →
        (∑' n : ℤ × ℤ, axis exceptional n * X ^ (n.1 + n.2)) * Q.eval X =
          X ^ m₀ * P.eval X := by
  have hc : ∃ (N : ℤ) (E : Polynomial ℂ) (M : ℕ), E.eval 0 ≠ 0 ∧
      (∀ t : ℤ, t < N → (∑ᶠ n : ℤ × ℤ,
        if (1 : ℤ) * n.1 + 1 * n.2 = t then axis exceptional n else 0) = 0) ∧
      (∀ m : ℕ, M ≤ m → ∑ i ∈ Finset.range (E.natDegree + 1),
        E.coeff i * (∑ᶠ n : ℤ × ℤ,
          if (1 : ℤ) * n.1 + 1 * n.2 = N + (m : ℤ) - (i : ℤ)
          then axis exceptional n else 0) = 0) := by
    refine ⟨-2, exceptionalAnnihilator, 3, by simp [exceptionalAnnihilator],
      ?_, ?_⟩
    · intro t ht
      simpa only [one_mul, axis_shell] using exceptional_support t ht
    · intro m hm
      simpa only [one_mul] using exceptional_axis_recurrence m hm
  obtain ⟨P, Q, m₀, hQ, h⟩ := source_laurent (axis exceptional) (-2)
    exceptional_axis_support 1 1 (by omega) (by omega) hc
  refine ⟨P, Q, m₀, hQ, fun X hpos hx => ?_⟩
  have hs := (axis_norm_summable exceptional X
    (exceptional_norm_summable X hx)).of_norm
  simpa only [Nat.cast_one, one_mul] using
    h X (norm_pos_iff.mp hpos) (by simpa only [Nat.cast_one, one_mul] using hs)

def deltaNegative (t : ℤ) : ℂ := if t = -1 then 1 else 0

private theorem deltaNegative_hasSum (X : ℂ) :
    HasSum (fun t : ℤ => deltaNegative t * X ^ t) (X ^ (-1 : ℤ)) := by
  refine (hasSum_ite_eq (-1 : ℤ) (X ^ (-1 : ℤ))).congr_fun fun t => ?_
  by_cases ht : t = -1 <;> simp [deltaNegative, ht]

private theorem deltaNegative_norm_summable (X : ℂ) :
    Summable (fun t : ℤ => ‖deltaNegative t * X ^ t‖) := by
  refine (hasSum_ite_eq (-1 : ℤ) ‖X ^ (-1 : ℤ)‖).summable.congr fun t => ?_
  by_cases ht : t = -1 <;> simp [deltaNegative, ht]

/-- Retain the supplied polynomial rather than replace it to avoid its root. -/
theorem deltaNegative_laurent_identity (X : ℂ) (hX : X ≠ 0) :
    (∑' t : ℤ, deltaNegative t * X ^ t) * (1 - X) =
      X ^ (-1 : ℤ) * (1 - X) := by
  have h0 : ∀ t : ℤ, t < -1 → deltaNegative t = 0 := by
    intro t ht
    simp [deltaNegative, show t ≠ -1 by omega]
  have hrec : ∀ t : ℤ, 1 ≤ t →
      ∑ i ∈ Finset.range ((1 - Polynomial.X : Polynomial ℂ).natDegree + 1),
        (1 - Polynomial.X : Polynomial ℂ).coeff i *
          deltaNegative (t - (i : ℤ)) = 0 := by
    intro t ht
    rw [degree_difference]
    norm_num [Finset.sum_range_succ, coeff_sub, coeff_one, coeff_X,
      deltaNegative, show t ≠ -1 by omega, show t - 1 ≠ -1 by omega]
  have h := Polynomial.tsum_mul_eval_eq_zpow_mul_eval_of_recurrence
    deltaNegative (1 - Polynomial.X) (-1) 1 h0 hrec X hX
    (deltaNegative_hasSum X).summable
  have hp :
      (∑ j ∈ Finset.range ((1 : ℤ) - (-1)).toNat,
        C (∑ i ∈ Finset.range ((1 - Polynomial.X : Polynomial ℂ).natDegree + 1),
          (1 - Polynomial.X : Polynomial ℂ).coeff i *
            deltaNegative (-1 + (j : ℤ) - (i : ℤ))) * Polynomial.X ^ j) =
        1 - Polynomial.X := by
    rw [degree_difference]
    norm_num [Finset.sum_range_succ, coeff_sub, coeff_one, coeff_X,
      deltaNegative, map_ofNat]
    ring
  rw [hp] at h
  simpa using h

/-- Summability survives at the root of the supplied annihilator. -/
theorem supplied_annihilator_root_boundary :
    Summable (fun n : ℤ × ℤ =>
      axis deltaNegative n * (1 : ℂ) ^ (n.1 + n.2)) ∧
    (1 - Polynomial.X : Polynomial ℂ).eval 1 = 0 ∧
    (∑' n : ℤ × ℤ, axis deltaNegative n * (1 : ℂ) ^ (n.1 + n.2)) *
        (1 - (1 : ℂ)) = (1 : ℂ) ^ (-1 : ℤ) * (1 - 1) := by
  refine ⟨(axis_norm_summable deltaNegative 1
    (deltaNegative_norm_summable 1)).of_norm, by norm_num, ?_⟩
  rw [axis_tsum deltaNegative 1 (deltaNegative_norm_summable 1)]
  exact deltaNegative_laurent_identity 1 (by norm_num)

/-- Geometric mass on a zero-weight axis has an infinite supported fiber. -/
def geometricHalf (i : ℤ) : ℂ := if 0 ≤ i then (2 : ℂ) ^ (-i - 1) else 0

private theorem geometricHalf_nat (n : ℕ) :
    geometricHalf n = (1 / 2 : ℂ) * (1 / 2 : ℂ) ^ n := by
  unfold geometricHalf
  rw [ite_eq_left (show (0 : ℤ) ≤ n by omega),
    show -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) by omega,
    zpow_neg, zpow_natCast, ← inv_pow, pow_succ]
  norm_num [mul_comm]

theorem geometricHalf_hasSum : HasSum geometricHalf 1 := by
  have hr : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num [norm_div]
  have hp := (hasSum_geometric_of_norm_lt_one hr).mul_left (1 / 2 : ℂ)
  have hn : HasSum (fun n : ℕ => geometricHalf n) 1 := by
    have h : HasSum (fun n : ℕ => (1 / 2 : ℂ) * (1 / 2 : ℂ) ^ n) 1 := by
      convert hp using 1
      norm_num
    exact h.congr_fun fun n => geometricHalf_nat n
  have hneg : HasSum (fun n : ℕ => geometricHalf (-(n + 1))) 0 := by
    refine (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0).congr_fun fun n => ?_
    unfold geometricHalf
    rw [ite_eq_right (by omega)]
  simpa using hn.of_nat_of_neg_add_one hneg

theorem geometricHalf_norm_summable :
    Summable (fun i : ℤ => ‖geometricHalf i‖) := by
  apply summable_norm_of_nat_of_zero_below _ 0
  · have hg := summable_norm_geometric_of_norm_lt_one
      (show ‖(1 / 2 : ℂ)‖ < 1 by norm_num [norm_div])
    refine (hg.mul_left ‖(1 / 2 : ℂ)‖).congr fun n => ?_
    rw [geometricHalf_nat, norm_mul]
  · intro i hi
    simp [geometricHalf, show ¬ 0 ≤ i by omega]

theorem zero_weight_infinite_support :
    (Function.support (axis geometricHalf)).Infinite := by
  refine (Set.infinite_range_of_injective
    (f := fun k : ℕ => ((k : ℤ), (0 : ℤ))) ?_).mono ?_
  · intro a b hab
    have h : (a : ℤ) = (b : ℤ) := congrArg Prod.fst hab
    exact_mod_cast h
  · rintro _ ⟨k, rfl⟩
    simp only [Function.mem_support, axis, ite_true, geometricHalf,
      ite_eq_left (show (0 : ℤ) ≤ k by omega)]
    exact zpow_ne_zero _ (by norm_num)

theorem zero_weight_shells (t : ℤ) :
    (∑ᶠ n : ℤ × ℤ,
      if (0 : ℤ) * n.1 + 1 * n.2 = t then axis geometricHalf n else 0) = 0 := by
  simp only [zero_mul, one_mul, zero_add]
  by_cases ht : t = 0
  · subst t
    calc
      _ = ∑ᶠ n : ℤ × ℤ, axis geometricHalf n := by
        apply finsum_congr
        intro n
        by_cases hj : n.2 = 0 <;> simp [axis, hj]
      _ = 0 := finsum_of_infinite_support zero_weight_infinite_support
  · apply finsum_eq_zero_of_forall_eq_zero
    intro n
    by_cases hj : n.2 = 0
    · simp [hj, Ne.symm ht]
    · simp [axis, hj]

/-- A zero-weight regrouping discrepancy, not a failure of rationality. -/
theorem zero_weight_regrouping_boundary :
    (∀ t : ℤ, (∑ᶠ n : ℤ × ℤ,
      if (0 : ℤ) * n.1 + 1 * n.2 = t then axis geometricHalf n else 0) = 0) ∧
    Summable (fun n : ℤ × ℤ => ‖axis geometricHalf n‖) ∧
    (∑' n : ℤ × ℤ, axis geometricHalf n) = 1 := by
  have hf : Summable (fun i : ℤ => ‖geometricHalf i * (1 : ℂ) ^ i‖) := by
    simpa using geometricHalf_norm_summable
  refine ⟨zero_weight_shells, ?_, ?_⟩
  · simpa using axis_norm_summable geometricHalf 1 hf
  · simpa using (axis_tsum geometricHalf 1 hf).trans
      (by simpa using geometricHalf_hasSum.tsum_eq)

/-- The noncoprime weights also reach the public closure and Laurent APIs. -/
theorem noncoprime_laurent_application :
    ∃ (P Q : Polynomial ℂ) (m₀ : ℤ), Q ≠ 0 ∧
      ∀ X : ℂ, X ≠ 0 → ‖2 * X ^ 2‖ < 1 → ‖3 * X ^ 4‖ < 1 →
        (∑' n : ℤ × ℤ, weighted n * X ^ (2 * n.1 + 4 * n.2)) * Q.eval X =
          X ^ m₀ * P.eval X := by
  obtain ⟨P, Q, m₀, hQ, h⟩ := source_weighted_composite
    quadrant ramp 2 3 (by norm_num) (by norm_num) 2 4
    (by omega) (by omega) quadrant_hypotheses ramp_hypotheses
  exact ⟨P, Q, m₀, hQ, fun X hX h1 h2 =>
    h X hX (weighted_norm_summable X hX 2 4 h1 h2).of_norm⟩

theorem noncoprime_domain_nonempty :
    ∃ X : ℂ, X ≠ 0 ∧ ‖2 * X ^ 2‖ < 1 ∧ ‖3 * X ^ 4‖ < 1 := by
  exact ⟨1 / 12, by norm_num [norm_mul, norm_pow, norm_div]⟩

/-- Overlapping cutoffs produce an empty residual interval, without division. -/
theorem empty_residual_interval (h : ℤ → ℂ) (q : Polynomial ℂ) (N T : ℤ)
    (hTN : T ≤ N) (h0 : ∀ t : ℤ, t < N → h t = 0)
    (hrec : ∀ t : ℤ, T ≤ t →
      ∑ i ∈ Finset.range (q.natDegree + 1),
        q.coeff i * h (t - (i : ℤ)) = 0)
    (X : ℂ) (hX : X ≠ 0) (hs : Summable (fun t : ℤ => h t * X ^ t)) :
    (∑' t : ℤ, h t * X ^ t) * q.eval X = 0 := by
  have hr := Polynomial.tsum_mul_eval_eq_zpow_mul_eval_of_recurrence
    h q N T h0 hrec X hX hs
  have hn : (T - N).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
  simpa only [hn, Finset.range_zero, Finset.sum_empty, eval_zero, mul_zero]
    using hr

/-!
The audit also describes weights (0,1) on the nonnegative quadrant with
w(i,j) = 2^(-i-1) / j!. Its line finsums vanish and its analytic sum is exp(X).
The global nonrationality argument for that stronger countermodel is not
formalized here. The proved geometric-axis mismatch above is only a failure
of this regrouping method; its true sum 1 is itself Laurent-rational.
-/

end LaurentRecurrenceTest
