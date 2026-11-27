/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The exact-source consumer below adapts the statement in
Theorems/
Source filename (concatenate the next two lines):
Thm_Polynomial_exists_mvPolynomial_forall_hasSum_torusWeight_mul_eq_of_
separated_recurrence.lean
from Fermat's Last Theorem in Lean 4, revision
6e837e75355538c7f80bab5b956861e86c4eacc2.
Copyright 2026 Anthropic, PBC. Licensed under Apache License, Version 2.0.
The original source identifies no individual authors. See NOTICE and
ATTRIBUTION.md there. Applications and boundary proofs are new.
-/
module

public import MathlibExt.Analysis.Analytic.SeparatedTorus
public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic.ComputeDegree

/-! # Importing consumers of the uniform torus-weight certificate -/

noncomputable section
open Finset Polynomial

namespace SeparatedTorusTest

/-- The original concrete source statement, without any extra hypothesis. -/
public theorem exactSource
    (A : ℤ × ℤ → ℂ) (N₁ : ℤ) (D₁ D₂ : Polynomial ℂ) (M : ℕ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N₁ ∨ n.2 < N₁) → A n = 0)
    (hrec : ∀ m₁ m₂ : ℕ, (M ≤ m₁ ∨ M ≤ m₂) →
      ∑ i ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
        D₁.coeff i * D₂.coeff l *
          A (N₁ + (m₁ : ℤ) - (i : ℤ), N₁ + (m₂ : ℤ) - (l : ℤ)) = 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ, ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧
      ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
          (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
            X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ,
          A (N₁ + (m.1 : ℤ), N₁ + (m.2 : ℤ)) *
            (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
              X ^ m.1 * Y ^ m.2) *
        (D₁.eval (b₁ * X) * D₁.eval (b₂ * X) * D₂.eval Y) =
        MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by
  obtain ⟨P, _, hP⟩ := Polynomial.exists_torusWeight_sum A N₁ D₁ D₂ M
    hD₁ hD₂ hsupp hrec
  exact ⟨P, hP⟩

private def seq (f : ℕ → ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then f n.toNat else 0

private def array (N : ℤ) (f g : ℕ → ℂ) (n : ℤ × ℤ) : ℂ :=
  seq f (n.1 - N) * seq g (n.2 - N)

private theorem array_nat (N : ℤ) (f g : ℕ → ℂ) (m k : ℕ) :
    array N f g (N + m, N + k) = f m * g k := by
  simp [array, seq]

private theorem array_support (N : ℤ) (f g : ℕ → ℂ) :
    ∀ n : ℤ × ℤ, (n.1 < N ∨ n.2 < N) → array N f g n = 0 := by
  intro n hn
  rcases hn with h | h
  · simp [array, seq, not_le.mpr h]
  · simp [array, seq, not_le.mpr h]

private theorem array_convolution (N : ℤ) (f g : ℕ → ℂ)
    (D₁ D₂ : Polynomial ℂ) (m k : ℕ) :
    (∑ i ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
      D₁.coeff i * D₂.coeff l *
        array N f g (N + (m : ℤ) - i, N + (k : ℤ) - l)) =
    (∑ i ∈ range (D₁.natDegree + 1), D₁.coeff i * seq f ((m : ℤ) - i)) *
      (∑ l ∈ range (D₂.natDegree + 1), D₂.coeff l * seq g ((k : ℤ) - l)) := by
  rw [sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
  dsimp [array]
  rw [show N + (m : ℤ) - i - N = (m : ℤ) - i by ring,
    show N + (k : ℤ) - l - N = (k : ℤ) - l by ring]
  ring

private def fibD : Polynomial ℂ := 1 - X - X ^ 2

private theorem fibD_degree : fibD.natDegree = 2 := by
  unfold fibD
  compute_degree!

private theorem fib_recurrence (m : ℕ) (hm : 2 ≤ m) :
    (∑ i ∈ range (fibD.natDegree + 1),
      fibD.coeff i * seq (fun n => (Nat.fib (n + 1) : ℂ)) ((m : ℤ) - i)) = 0 :=
          by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 2 := ⟨m - 2, by omega⟩
  have h0 : (0 : ℤ) ≤ n + 2 := by omega
  have h1 : (1 : ℤ) ≤ n + 2 := by omega
  have hn : ((n : ℤ) + 2).toNat = n + 2 := by omega
  rw [fibD_degree]
  norm_num [fibD, sum_range_succ, seq, coeff_one, coeff_X, h0, h1, hn]
  rw [show n + 2 + 1 = n + 1 + 2 by omega, Nat.fib_add_two]
  push_cast
  ring

private def geoD : Polynomial ℂ := 1 - C 3 * X

private theorem geoD_degree : geoD.natDegree = 1 := by
  unfold geoD
  compute_degree!

private theorem geo_recurrence (k : ℕ) (hk : 1 ≤ k) :
    (∑ l ∈ range (geoD.natDegree + 1),
      geoD.coeff l * seq (fun n => (3 : ℂ) ^ n) ((k : ℤ) - l)) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = n + 1 := ⟨k - 1, by omega⟩
  have h0 : (0 : ℤ) ≤ n + 1 := by omega
  have hn : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [geoD_degree]
  norm_num [geoD, sum_range_succ, seq, coeff_one, coeff_C_mul, coeff_X, h0, hn]
  ring

private theorem fib_array_recurrence (m k : ℕ) (hmk : 2 ≤ m ∨ 2 ≤ k) :
    (∑ i ∈ range (fibD.natDegree + 1), ∑ l ∈ range (geoD.natDegree + 1),
      fibD.coeff i * geoD.coeff l *
        array 0 (fun n => (Nat.fib (n + 1) : ℂ)) (fun n => (3 : ℂ) ^ n)
          (0 + (m : ℤ) - i, 0 + (k : ℤ) - l)) = 0 := by
  rw [array_convolution]
  rcases hmk with hm | hk
  · rw [fib_recurrence m hm, zero_mul]
  · rw [geo_recurrence k (by omega), mul_zero]

set_option maxHeartbeats 1000000 in
/-- Fibonacci coefficients with a nonconstant second-coordinate denominator. -/
public theorem fibonacci :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      P = 1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ =>
          ‖(Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
            (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
              X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, (Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
          (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
            X ^ m.1 * Y ^ m.2) *
          ((1 - b₁ * X - (b₁ * X) ^ 2) *
            (1 - b₂ * X - (b₂ * X) ^ 2) * (1 - 3 * Y)) =
          MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by
  obtain ⟨P, hP, h⟩ := Polynomial.exists_torusWeight_sum
    (array 0 (fun n => (Nat.fib (n + 1) : ℂ)) (fun n => (3 : ℂ) ^ n))
    0 fibD geoD 2 (by norm_num [fibD]) (by norm_num [geoD])
    (array_support _ _ _) fib_array_recurrence
  refine ⟨P, ?_, ?_⟩
  · rw [fibD_degree] at hP
    simp only [fibD, geoD, coeff_sub, coeff_one, coeff_X, coeff_X_pow,
      coeff_C_mul] at hP
    rw [hP]
    norm_num [array, seq, sum_range_succ, Nat.fib_add_two]
    norm_num only [map_ofNat]
    ring
  · simpa only [array_nat, fibD, geoD, eval_sub, eval_one, eval_X, eval_pow,
      eval_mul, eval_C] using h

private def repeatD (c : ℂ) : Polynomial ℂ := (1 - C c * X) ^ 2

private theorem repeatD_expanded (c : ℂ) :
    repeatD c = 1 - C (c + c) * X + C (c * c) * X ^ 2 := by
  simp only [repeatD, map_add, map_mul]
  ring

private theorem repeatD_two_degree : (repeatD 2).natDegree = 2 := by
  unfold repeatD
  compute_degree!

private theorem repeatD_three_degree : (repeatD 3).natDegree = 2 := by
  unfold repeatD
  compute_degree!

private theorem repeat_recurrence (c : ℂ) (hd : (repeatD c).natDegree = 2)
    (m : ℕ) (hm : 2 ≤ m) :
    (∑ i ∈ range ((repeatD c).natDegree + 1),
      (repeatD c).coeff i * seq (fun n => (n + 1 : ℂ) * c ^ n) ((m : ℤ) - i)) =
          0 := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = n + 2 := ⟨m - 2, by omega⟩
  have h0 : (0 : ℤ) ≤ n + 2 := by omega
  have h1 : (1 : ℤ) ≤ n + 2 := by omega
  have hn : ((n : ℤ) + 2).toNat = n + 2 := by omega
  rw [hd, repeatD_expanded]
  simp only [coeff_add, coeff_sub, coeff_one, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num [sum_range_succ, seq, h0, h1, hn]
  ring

private theorem repeat_array_recurrence (m k : ℕ) (hmk : 2 ≤ m ∨ 2 ≤ k) :
    (∑ i ∈ range ((repeatD 2).natDegree + 1),
      ∑ l ∈ range ((repeatD 3).natDegree + 1),
        (repeatD 2).coeff i * (repeatD 3).coeff l *
          array (-2) (fun n => (n + 1 : ℂ) * 2 ^ n) (fun n => (n + 1 : ℂ) * 3 ^
              n)
            (-2 + (m : ℤ) - i, -2 + (k : ℤ) - l)) = 0 := by
  rw [array_convolution]
  rcases hmk with hm | hk
  · rw [repeat_recurrence 2 repeatD_two_degree m hm, zero_mul]
  · rw [repeat_recurrence 3 repeatD_three_degree k hk, mul_zero]

set_option maxHeartbeats 2000000 in
/-- Repeated poles in both coordinates, obtained at the original support shift
  `-2`. -/
public theorem repeatedPoles :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      P = 1 - 4 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ =>
          ‖((m.1 + 1 : ℂ) * 2 ^ m.1) * ((m.2 + 1 : ℂ) * 3 ^ m.2) *
            (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
              X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, ((m.1 + 1 : ℂ) * 2 ^ m.1) *
          ((m.2 + 1 : ℂ) * 3 ^ m.2) *
            (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
              X ^ m.1 * Y ^ m.2) *
          ((1 - 2 * (b₁ * X)) ^ 2 * (1 - 2 * (b₂ * X)) ^ 2 *
            (1 - 3 * Y) ^ 2) =
          MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by
  obtain ⟨P, hP, h⟩ := Polynomial.exists_torusWeight_sum
    (array (-2) (fun n => (n + 1 : ℂ) * 2 ^ n) (fun n => (n + 1 : ℂ) * 3 ^ n))
    (-2) (repeatD 2) (repeatD 3) 2 (by norm_num [repeatD]) (by norm_num
        [repeatD])
    (array_support _ _ _) repeat_array_recurrence
  refine ⟨P, ?_, ?_⟩
  · rw [repeatD_two_degree] at hP
    simp only [repeatD_expanded, coeff_add, coeff_sub, coeff_one, coeff_C_mul,
      coeff_X_pow, coeff_X] at hP
    rw [hP]
    norm_num [array, seq, sum_range_succ]
    norm_num only [map_ofNat]
    ring
  · simpa only [array_nat, repeatD, eval_pow, eval_sub, eval_one, eval_mul,
      eval_C, eval_X] using h

/-- Confluence is the canonical two-variable geometric-sum identity, not
  division. -/
public theorem weight_self (b : ℂ) (m : ℕ) :
    (∑ i ∈ range (m + 1), b ^ i * b ^ (m - i)) = (m + 1 : ℂ) * b ^ m := by
  simpa using geom_sum₂_self b (m + 1)

/-- A zero first parameter leaves only the `i = 0` summand. -/
public theorem weight_zero_left (b : ℂ) (m : ℕ) :
    (∑ i ∈ range (m + 1), (0 : ℂ) ^ i * b ^ (m - i)) = b ^ m := by
  rw [sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · simp

/-- A zero second parameter leaves only the `i = m` summand. -/
public theorem weight_zero_right (b : ℂ) (m : ℕ) :
    (∑ i ∈ range (m + 1), b ^ i * (0 : ℂ) ^ (m - i)) = b ^ m := by
  rw [sum_eq_single m]
  · simp
  · intro i hi him
    have hn : m - i ≠ 0 := by have := mem_range.mp hi; omega
    simp [zero_pow hn]
  · simp

/-- The constant summand survives at `(0, 0)`, including `0 ^ 0 = 1`. -/
public theorem weight_zero_zero (m : ℕ) :
    (∑ i ∈ range (m + 1), (0 : ℂ) ^ i * (0 : ℂ) ^ (m - i)) =
      if m = 0 then 1 else 0 := by
  rw [weight_zero_left]
  split_ifs with hm
  · simp [hm]
  · exact zero_pow hm

/-- The confluent repeated-root coefficient is quadratic in the index. -/
public theorem repeated_weight_self (b : ℂ) (m : ℕ) :
    ((m + 1 : ℂ) * 2 ^ m) *
      (∑ i ∈ range (m + 1), b ^ i * b ^ (m - i)) =
        (m + 1 : ℂ) ^ 2 * (2 * b) ^ m := by
  rw [weight_self, mul_pow]
  ring

/-- One Fibonacci certificate covers every listed boundary pair, with positive
  radii. -/
public theorem fibonacci_boundary_pairs :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      P = 1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      ∀ b : ℂ, ∀ p ∈ [(b, b), (0, b), (b, 0), (0, 0), (Complex.I, -Complex.I)],
        ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
          Summable (fun m : ℕ × ℕ =>
            ‖(Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
              (∑ i ∈ range (m.1 + 1), p.1 ^ i * p.2 ^ (m.1 - i)) *
                X ^ m.1 * Y ^ m.2‖) ∧
          (∑' m : ℕ × ℕ, (Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
            (∑ i ∈ range (m.1 + 1), p.1 ^ i * p.2 ^ (m.1 - i)) *
              X ^ m.1 * Y ^ m.2) *
            ((1 - p.1 * X - (p.1 * X) ^ 2) *
              (1 - p.2 * X - (p.2 * X) ^ 2) * (1 - 3 * Y)) =
            1 + X ^ 2 * p.1 * p.2 := by
  obtain ⟨P, hP, h⟩ := fibonacci
  refine ⟨P, hP, ?_⟩
  intro b p _
  obtain ⟨r, hr, h⟩ := h p.1 p.2
  exact ⟨r, hr, fun X Y hX hY => by simpa [hP] using h X Y hX hY⟩

/-- The repeated-pole certificate admits the same confluence, zero and imaginary
  pairs. -/
public theorem repeatedPoles_boundary_pairs :
    ∃ P : MvPolynomial (Fin 4) ℂ,
      P = 1 - 4 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 2 * MvPolynomial.X 3 ∧
      ∀ b : ℂ, ∀ p ∈ [(b, b), (0, b), (b, 0), (0, 0), (Complex.I, -Complex.I)],
        ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
          Summable (fun m : ℕ × ℕ =>
            ‖((m.1 + 1 : ℂ) * 2 ^ m.1) * ((m.2 + 1 : ℂ) * 3 ^ m.2) *
              (∑ i ∈ range (m.1 + 1), p.1 ^ i * p.2 ^ (m.1 - i)) *
                X ^ m.1 * Y ^ m.2‖) ∧
          (∑' m : ℕ × ℕ, ((m.1 + 1 : ℂ) * 2 ^ m.1) *
            ((m.2 + 1 : ℂ) * 3 ^ m.2) *
              (∑ i ∈ range (m.1 + 1), p.1 ^ i * p.2 ^ (m.1 - i)) *
                X ^ m.1 * Y ^ m.2) *
            ((1 - 2 * (p.1 * X)) ^ 2 * (1 - 2 * (p.2 * X)) ^ 2 *
              (1 - 3 * Y) ^ 2) = 1 - 4 * X ^ 2 * p.1 * p.2 := by
  obtain ⟨P, hP, h⟩ := repeatedPoles
  refine ⟨P, hP, ?_⟩
  intro b p _
  obtain ⟨r, hr, h⟩ := h p.1 p.2
  exact ⟨r, hr, fun X Y hX hY => by simpa [hP] using h X Y hX hY⟩

/-- The Fibonacci confluent rational identity retains a positive
  norm-summability radius. -/
public theorem fibonacci_equal (b : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖(Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
          ((m.1 + 1 : ℂ) * b ^ m.1) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, (Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
        ((m.1 + 1 : ℂ) * b ^ m.1) * X ^ m.1 * Y ^ m.2) *
        ((1 - b * X - (b * X) ^ 2) ^ 2 * (1 - 3 * Y)) =
        1 + X ^ 2 * b * b := by
  obtain ⟨P, hP, h⟩ := fibonacci
  obtain ⟨r, hr, h⟩ := h b b
  exact ⟨r, hr, fun X Y hX hY => by
    simpa [hP, weight_self, pow_two] using h X Y hX hY⟩

/-- Confluence raises the first-coordinate multiplicity while preserving the
  negative shift. -/
public theorem repeatedPoles_equal (b : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖((m.1 + 1 : ℂ) ^ 2 * (2 * b) ^ m.1) *
          ((m.2 + 1 : ℂ) * 3 ^ m.2) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, ((m.1 + 1 : ℂ) ^ 2 * (2 * b) ^ m.1) *
        ((m.2 + 1 : ℂ) * 3 ^ m.2) * X ^ m.1 * Y ^ m.2) *
        ((1 - 2 * (b * X)) ^ 4 * (1 - 3 * Y) ^ 2) =
        1 - 4 * X ^ 2 * b * b := by
  obtain ⟨P, hP, h⟩ := repeatedPoles
  obtain ⟨r, hr, h⟩ := h b b
  have ht (m : ℕ × ℕ) : ((m.1 + 1 : ℂ) * 2 ^ m.1) *
      ((m.2 + 1 : ℂ) * 3 ^ m.2) *
        (∑ i ∈ range (m.1 + 1), b ^ i * b ^ (m.1 - i)) =
      ((m.1 + 1 : ℂ) ^ 2 * (2 * b) ^ m.1) * ((m.2 + 1 : ℂ) * 3 ^ m.2) := by
    rw [mul_right_comm, repeated_weight_self]
  refine ⟨r, hr, fun X Y hX hY => ?_⟩
  have hx := h X Y hX hY
  simp only [ht] at hx
  simpa [hP, ← pow_add] using hx

/-- With threshold zero, the nonzero constant coefficient solves every
  total-index step. -/
public theorem threshold_zero
    (A : ℤ × ℤ → ℂ) (N : ℤ) (D₁ D₂ : Polynomial ℂ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0)
    (hsupp : ∀ n : ℤ × ℤ, (n.1 < N ∨ n.2 < N) → A n = 0)
    (hrec : ∀ m k : ℕ, (0 ≤ m ∨ 0 ≤ k) →
      ∑ i ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
        D₁.coeff i * D₂.coeff l * A (N + (m : ℤ) - i, N + (k : ℤ) - l) = 0) :
    A = 0 := by
  have hc₁ : D₁.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have hc₂ : D₂.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have ha : ∀ n m k : ℕ, m + k = n → A (N + (m : ℤ), N + (k : ℤ)) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro m k hmk
      have hz (i l : ℕ) (hne : i ≠ 0 ∨ l ≠ 0) :
          A (N + (m : ℤ) - i, N + (k : ℤ) - l) = 0 := by
        by_cases hi : i ≤ m
        · by_cases hl : l ≤ k
          · have hlt : (m - i) + (k - l) < n := by omega
            have he₁ : N + (m : ℤ) - i = N + ((m - i : ℕ) : ℤ) := by omega
            have he₂ : N + (k : ℤ) - l = N + ((k - l : ℕ) : ℤ) := by omega
            rw [he₁, he₂]
            exact ih _ hlt _ _ rfl
          · exact hsupp _ (Or.inr (by dsimp; omega))
        · exact hsupp _ (Or.inl (by dsimp; omega))
      have he : (∑ i ∈ range (D₁.natDegree + 1), ∑ l ∈ range (D₂.natDegree + 1),
          D₁.coeff i * D₂.coeff l * A (N + (m : ℤ) - i, N + (k : ℤ) - l)) =
          D₁.coeff 0 * D₂.coeff 0 * A (N + (m : ℤ), N + (k : ℤ)) := by
        rw [sum_eq_single 0]
        · rw [sum_eq_single 0]
          · simp
          · intro l _ hl
            rw [hz 0 l (Or.inr hl), mul_zero]
          · simp
        · intro i _ hi
          apply sum_eq_zero
          intro l _
          rw [hz i l (Or.inl hi), mul_zero]
        · simp
      have hh := hrec m k (Or.inl (Nat.zero_le _))
      rw [he] at hh
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero hc₁ hc₂)
  funext p
  change A p = 0
  by_cases h₁ : p.1 < N
  · exact hsupp p (Or.inl h₁)
  by_cases h₂ : p.2 < N
  · exact hsupp p (Or.inr h₂)
  have he₁ : N + (((p.1 - N).toNat : ℕ) : ℤ) = p.1 := by omega
  have he₂ : N + (((p.2 - N).toNat : ℕ) : ℤ) = p.2 := by omega
  simpa only [he₁, he₂, Prod.eta] using
    ha ((p.1 - N).toNat + (p.2 - N).toNat) (p.1 - N).toNat (p.2 - N).toNat rfl

private def factorialAxis (n : ℤ × ℤ) : ℂ :=
  if n.2 = 0 ∧ 0 ≤ n.1 then (Nat.factorial n.1.toNat : ℂ) else 0

private def axisD : Polynomial ℂ := 1 - X

private theorem axisD_degree : axisD.natDegree = 1 := by
  unfold axisD
  compute_degree!

/-- The factorial-axis fixture has the same lower support as the source. -/
theorem factorial_axis_support :
    ∀ n : ℤ × ℤ, (n.1 < 0 ∨ n.2 < 0) → factorialAxis n = 0 := by
  intro n hn
  rcases hn with h | h
  · simp [factorialAxis, not_le.mpr h]
  · simp [factorialAxis, ne_of_lt h]

/-- An AND exterior condition leaves the entire horizontal axis unchecked. -/
theorem factorial_axis_and (m k : ℕ) (h : 2 ≤ m ∧ 2 ≤ k) :
    (∑ i ∈ range (axisD.natDegree + 1), ∑ l ∈ range ((1 : Polynomial
        ℂ).natDegree + 1),
      axisD.coeff i * (1 : Polynomial ℂ).coeff l *
        factorialAxis ((m : ℤ) - i, (k : ℤ) - l)) = 0 := by
  have hk : k ≠ 0 := by omega
  rw [axisD_degree]
  simp [axisD, coeff_one, coeff_X, factorialAxis, hk]

/-- The OR condition really fails: the residual at `(5, 0)` is `120 - 24`. -/
theorem factorial_axis_residual :
    (∑ i ∈ range (axisD.natDegree + 1), ∑ l ∈ range ((1 : Polynomial
        ℂ).natDegree + 1),
      axisD.coeff i * (1 : Polynomial ℂ).coeff l *
        factorialAxis ((5 : ℤ) - i, (0 : ℤ) - l)) = 96 := by
  rw [axisD_degree]
  norm_num [axisD, sum_range_succ, coeff_one, coeff_X, factorialAxis,
      Nat.factorial]

/-- This proves failure of OR, not a zero-radius or nonrationality claim. -/
theorem factorial_axis_not_or :
    ¬ (∀ m k : ℕ, (2 ≤ m ∨ 2 ≤ k) →
      (∑ i ∈ range (axisD.natDegree + 1),
        ∑ l ∈ range ((1 : Polynomial ℂ).natDegree + 1),
          axisD.coeff i * (1 : Polynomial ℂ).coeff l *
            factorialAxis ((m : ℤ) - i, (k : ℤ) - l)) = 0) := by
  intro h
  have hz := h 5 0 (Or.inl (by norm_num))
  norm_num only [Nat.cast_ofNat, Nat.cast_zero] at hz
  rw [factorial_axis_residual] at hz
  norm_num at hz

/-- Nonzero constant denominators also accept a nonzero finitely supported
  array. -/
public theorem constant_denominators :
    ∃ P : MvPolynomial (Fin 4) ℂ, P = MvPolynomial.C 60 ∧
      ∀ b₁ b₂ : ℂ, ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun m : ℕ × ℕ =>
          ‖(if m.1 = 0 ∧ m.2 = 0 then (5 : ℂ) else 0) *
            (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
              X ^ m.1 * Y ^ m.2‖) ∧
        (∑' m : ℕ × ℕ, (if m.1 = 0 ∧ m.2 = 0 then (5 : ℂ) else 0) *
          (∑ i ∈ range (m.1 + 1), b₁ ^ i * b₂ ^ (m.1 - i)) *
            X ^ m.1 * Y ^ m.2) * 12 =
          MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by
  let A : ℤ × ℤ → ℂ := fun n => if n = (0, 0) then 5 else 0
  have hs : ∀ n : ℤ × ℤ, (n.1 < 0 ∨ n.2 < 0) → A n = 0 := by
    intro n hn
    dsimp [A]
    split_ifs with h
    · subst n
      norm_num at hn
    · rfl
  have hr : ∀ m k : ℕ, (1 ≤ m ∨ 1 ≤ k) →
      (∑ i ∈ range ((C 2 : Polynomial ℂ).natDegree + 1),
        ∑ l ∈ range ((C 3 : Polynomial ℂ).natDegree + 1),
          (C 2 : Polynomial ℂ).coeff i * (C 3 : Polynomial ℂ).coeff l *
            A (0 + (m : ℤ) - i, 0 + (k : ℤ) - l)) = 0 := by
    intro m k hm
    have hn : ¬ (m = 0 ∧ k = 0) := by omega
    simp [A, Prod.ext_iff, hn]
  obtain ⟨P, hP, h⟩ := Polynomial.exists_torusWeight_sum A 0 (C 2) (C 3) 1
    (by norm_num) (by norm_num) hs hr
  refine ⟨P, ?_, ?_⟩
  · rw [hP]
    norm_num [A, sum_range_succ, coeff_C, Prod.ext_iff]
  · simpa [A, Prod.ext_iff, show (2 * 2 * 3 : ℂ) = 12 by norm_num] using h

/-- Setting one parameter to zero removes one Fibonacci denominator factor. -/
public theorem fibonacci_zero (b : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖(Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 * b ^ m.1 *
          X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, (Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 * b ^ m.1 *
        X ^ m.1 * Y ^ m.2) *
        ((1 - b * X - (b * X) ^ 2) * (1 - 3 * Y)) = 1 := by
  obtain ⟨P, hP, h⟩ := fibonacci
  obtain ⟨r, hr, h⟩ := h 0 b
  exact ⟨r, hr, fun X Y hX hY => by
    simpa [hP, weight_zero_left] using h X Y hX hY⟩

/-- The repeated-pole zero specialization still has a nonconstant `Y`
  denominator. -/
public theorem repeatedPoles_zero (b : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖((m.1 + 1 : ℂ) * 2 ^ m.1) * ((m.2 + 1 : ℂ) * 3 ^ m.2) *
          b ^ m.1 * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, ((m.1 + 1 : ℂ) * 2 ^ m.1) *
        ((m.2 + 1 : ℂ) * 3 ^ m.2) * b ^ m.1 * X ^ m.1 * Y ^ m.2) *
        ((1 - 2 * (b * X)) ^ 2 * (1 - 3 * Y) ^ 2) = 1 := by
  obtain ⟨P, hP, h⟩ := repeatedPoles
  obtain ⟨r, hr, h⟩ := h 0 b
  exact ⟨r, hr, fun X Y hX hY => by
    simpa [hP, weight_zero_left] using h X Y hX hY⟩

/-- Both zero parameters retain exactly the `m = 0` slice of the Fibonacci
  array. -/
public theorem fibonacci_both_zero :
    ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖(Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
          (if m.1 = 0 then 1 else 0) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, (Nat.fib (m.1 + 1) : ℂ) * (3 : ℂ) ^ m.2 *
        (if m.1 = 0 then 1 else 0) * X ^ m.1 * Y ^ m.2) * (1 - 3 * Y) = 1 := by
  obtain ⟨P, hP, h⟩ := fibonacci
  obtain ⟨r, hr, h⟩ := h 0 0
  exact ⟨r, hr, fun X Y hX hY => by
    simpa [hP, weight_zero_zero] using h X Y hX hY⟩

/-- Both zero parameters retain exactly the `m = 0` repeated-pole slice. -/
public theorem repeatedPoles_both_zero :
    ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
      Summable (fun m : ℕ × ℕ =>
        ‖((m.1 + 1 : ℂ) * 2 ^ m.1) * ((m.2 + 1 : ℂ) * 3 ^ m.2) *
          (if m.1 = 0 then 1 else 0) * X ^ m.1 * Y ^ m.2‖) ∧
      (∑' m : ℕ × ℕ, ((m.1 + 1 : ℂ) * 2 ^ m.1) *
        ((m.2 + 1 : ℂ) * 3 ^ m.2) * (if m.1 = 0 then 1 else 0) *
          X ^ m.1 * Y ^ m.2) * (1 - 3 * Y) ^ 2 = 1 := by
  obtain ⟨P, hP, h⟩ := repeatedPoles
  obtain ⟨r, hr, h⟩ := h 0 0
  exact ⟨r, hr, fun X Y hX hY => by
    simpa [hP, weight_zero_zero] using h X Y hX hY⟩

/-- The negative support shift is real: its corner is nonzero and either lower
  edge is zero. -/
theorem repeatedPoles_support_boundary :
    array (-2) (fun n => (n + 1 : ℂ) * 2 ^ n) (fun n => (n + 1 : ℂ) * 3 ^ n)
        (-2, -2) = 1 ∧
      array (-2) (fun n => (n + 1 : ℂ) * 2 ^ n) (fun n => (n + 1 : ℂ) * 3 ^ n)
        (-3, -2) = 0 ∧
      array (-2) (fun n => (n + 1 : ℂ) * 2 ^ n) (fun n => (n + 1 : ℂ) * 3 ^ n)
        (-2, -3) = 0 := by
  norm_num [array, seq]

/-- The main API itself admits `M = 0`, with an empty polynomial witness. -/
public theorem zero_threshold_certificate (N : ℤ) (D₁ D₂ : Polynomial ℂ)
    (hD₁ : D₁.eval 0 ≠ 0) (hD₂ : D₂.eval 0 ≠ 0) :
    ∃ P : MvPolynomial (Fin 4) ℂ, P = 0 ∧ ∀ b₁ b₂ : ℂ,
      ∃ r : ℝ, 0 < r ∧ ∀ X Y : ℂ, ‖X‖ < r → ‖Y‖ < r →
        Summable (fun _ : ℕ × ℕ => ‖(0 : ℂ)‖) ∧
          (0 : ℂ) = MvPolynomial.eval (![X, Y, b₁, b₂] : Fin 4 → ℂ) P := by
  obtain ⟨P, hP, h⟩ := Polynomial.exists_torusWeight_sum (fun _ => 0) N D₁ D₂ 0
    hD₁ hD₂ (by simp) (by simp)
  exact ⟨P, by simpa using hP, by simpa using h⟩

/-- On the original integer quadrant, the fixture has exactly the stated shifted
  coefficients. -/
theorem repeatedPoles_unshifted (i j : ℤ) (hi : -2 ≤ i) (hj : -2 ≤ j) :
    array (-2) (fun n => (n + 1 : ℂ) * 2 ^ n) (fun n => (n + 1 : ℂ) * 3 ^ n)
        (i, j) =
      (((i + 3 : ℤ) : ℂ) * 2 ^ (i + 2).toNat) *
        (((j + 3 : ℤ) : ℂ) * 3 ^ (j + 2).toNat) := by
  have hmi : ((i + 2).toNat : ℤ) = i + 2 := by omega
  have hmj : ((j + 2).toNat : ℤ) = j + 2 := by omega
  have hci : ((i + 2).toNat : ℂ) = (i : ℂ) + 2 := by exact_mod_cast hmi
  have hcj : ((j + 2).toNat : ℂ) = (j : ℂ) + 2 := by exact_mod_cast hmj
  have hni : 0 ≤ i + 2 := by omega
  have hnj : 0 ≤ j + 2 := by omega
  norm_num [array, seq, hni, hnj, hci, hcj, add_assoc]

end SeparatedTorusTest
