/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Sequences.Unimodal
public import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Order.Interval.Finset.Nat

/-!
# Products of symmetric unimodal polynomials

A symmetric unimodal sequence of nonnegative coefficients is a nonnegative sum of
concentric interval indicators. Products of two such indicators have trapezoidal
coefficient profiles, all centered at the same index or half-index.
-/

open Finset Polynomial MathlibExt.Combinatorics.Sequences.Unimodal

namespace MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted

private lemma left_half_mono {f : ℕ → ℝ} {d : ℕ}
    (hs : ∀ i ≤ d, f i = f (d - i)) (hu : IsUnimodal f d) :
    ∀ i < d / 2, f i ≤ f (i + 1) := by
  obtain ⟨j, _, hup, hdown⟩ := hu
  intro i hi
  by_cases hij : i < j
  · exact hup i hij
  rw [hs i (by omega), hs (i + 1) (by omega),
    show d - i = d - (i + 1) + 1 by omega]
  exact hdown _ (by omega) (by omega)

private lemma unimodal_of_left_half {f : ℕ → ℝ} {d : ℕ}
    (hs : ∀ i ≤ d, f i = f (d - i)) (hm : ∀ i < d / 2, f i ≤ f (i + 1)) :
    IsUnimodal f d := by
  refine ⟨d / 2, by omega, hm, fun i hi hid => ?_⟩
  by_cases h : i + 1 = d - i
  · rw [h]
    exact (hs i hid.le).ge
  rw [hs i hid.le, hs (i + 1) hid, show d - i = d - (i + 1) + 1 by omega]
  exact hm _ (by omega)

private noncomputable def intervalPoly (a b : ℕ) : ℝ[X] :=
  ∑ i ∈ Icc a b, monomial i 1

private lemma coeff_intervalPoly (a b k : ℕ) :
    (intervalPoly a b).coeff k = if a ≤ k ∧ k ≤ b then 1 else 0 := by
  classical
  rw [intervalPoly, finsetSum_coeff]
  simp only [coeff_monomial_apply, Finset.sum_ite_eq', mem_Icc]

-- A pair with sum `k` belongs to the two intervals precisely when its first
-- coordinate is between `max a (k - e)` and `min b (k - c)` (provided `c ≤ k`).
private lemma coeff_intervalPoly_mul {a b c e : ℕ} (hab : a ≤ b) (hce : c ≤ e) (k : ℕ) :
    (intervalPoly a b * intervalPoly c e).coeff k =
      (min (min (k + 1 - (a + c)) (b + e + 1 - k)) (min (b + 1 - a) (e + 1 - c)) : ℕ) := by
  classical
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => (intervalPoly a b).coeff i * (intervalPoly c e).coeff j)]
  simp only [coeff_intervalPoly, ite_mul, one_mul, zero_mul, ← ite_and, ← Finset.sum_filter]
  by_cases hck : c ≤ k
  · have hfilter : (range (k + 1)).filter
        (fun i => (a ≤ i ∧ i ≤ b) ∧ (c ≤ k - i ∧ k - i ≤ e)) =
          Icc (max a (k - e)) (min b (k - c)) := by
      ext i
      simp only [mem_filter, mem_range, mem_Icc, max_le_iff, le_min_iff]
      omega
    rw [hfilter]
    simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc, Nat.cast_inj]
    omega
  · have hzero : (range (k + 1)).filter
        (fun i => (a ≤ i ∧ i ≤ b) ∧ (c ≤ k - i ∧ k - i ≤ e)) = ∅ := by
      ext i
      simp only [mem_filter, mem_range, notMem_empty, iff_false]
      omega
    rw [hzero, sum_empty, show k + 1 - (a + c) = 0 by omega]
    simp

private def layerWeight (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  f i - if i = 0 then 0 else f (i - 1)

private lemma layerWeight_nonneg {f : ℕ → ℝ} {d : ℕ} (h0 : 0 ≤ f 0)
    (hm : ∀ i < d / 2, f i ≤ f (i + 1)) {i : ℕ} (hi : i ≤ d / 2) :
    0 ≤ layerWeight f i := by
  cases i with
  | zero => simpa [layerWeight] using h0
  | succ i => simpa [layerWeight, sub_nonneg] using hm i (by omega)

private lemma sum_layerWeight (f : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range (k + 1), layerWeight f i = f k := by
  induction k with
  | zero => simp [layerWeight]
  | succ k ih => rw [sum_range_succ, ih]; simp [layerWeight]

private lemma eq_sum_layers {P : ℝ[X]} {d : ℕ} (hd : P.natDegree ≤ d)
    (hs : ∀ i ≤ d, P.coeff i = P.coeff (d - i)) :
    P = ∑ i ∈ range (d / 2 + 1), C (layerWeight P.coeff i) * intervalPoly i (d - i) := by
  ext k
  simp only [finsetSum_coeff, coeff_C_mul, coeff_intervalPoly, mul_ite, mul_one, mul_zero,
    ← sum_filter]
  by_cases hk : k ≤ d
  · have hfilter : (range (d / 2 + 1)).filter (fun i => i ≤ k ∧ k ≤ d - i) =
        range (min k (d - k) + 1) := by
      ext i
      simp only [mem_filter, mem_range]
      omega
    rw [hfilter, sum_layerWeight]
    by_cases h : k ≤ d - k
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega), ← hs k hk]
  · have hzero : (range (d / 2 + 1)).filter (fun i => i ≤ k ∧ k ≤ d - i) = ∅ := by
      ext i
      simp only [mem_filter, mem_range, notMem_empty, iff_false]
      omega
    rw [hzero, sum_empty, coeff_eq_zero_of_natDegree_lt (by omega)]

-- The two sloping sides have a common center independent of the layers `i` and `j`.
private def trapezoid (m n i j k : ℕ) : ℕ :=
  min (min (k + 1 - (i + j)) (m + n + 1 - (i + j) - k))
    (min (m + 1 - (i + i)) (n + 1 - (j + j)))

private lemma coeff_mul_layers {P Q : ℝ[X]} {m n : ℕ} (hPm : P.natDegree ≤ m)
    (hQn : Q.natDegree ≤ n) (hPs : ∀ i ≤ m, P.coeff i = P.coeff (m - i))
    (hQs : ∀ i ≤ n, Q.coeff i = Q.coeff (n - i)) (k : ℕ) :
    (P * Q).coeff k = ∑ i ∈ range (m / 2 + 1), ∑ j ∈ range (n / 2 + 1),
      layerWeight P.coeff i * layerWeight Q.coeff j * (trapezoid m n i j k : ℝ) := by
  let A (i : ℕ) := C (layerWeight P.coeff i) * intervalPoly i (m - i)
  let B (j : ℕ) := C (layerWeight Q.coeff j) * intervalPoly j (n - j)
  calc
    (P * Q).coeff k = ((∑ i ∈ range (m / 2 + 1), A i) *
        (∑ j ∈ range (n / 2 + 1), B j)).coeff k :=
      congrArg₂ (fun U V : ℝ[X] => (U * V).coeff k)
        (eq_sum_layers hPm hPs) (eq_sum_layers hQn hQs)
    _ = ∑ i ∈ range (m / 2 + 1), ∑ j ∈ range (n / 2 + 1), (A i * B j).coeff k := by
      rw [sum_mul]
      simp only [mul_sum, finsetSum_coeff]
    _ = _ := by
      refine sum_congr rfl fun i hi => sum_congr rfl fun j hj => ?_
      rw [mem_range] at hi hj
      dsimp only [A, B]
      rw [mul_mul_mul_comm, ← (C : ℝ →+* ℝ[X]).map_mul, coeff_C_mul,
        coeff_intervalPoly_mul (by omega) (by omega)]
      unfold trapezoid
      rw [show m - i + (n - j) + 1 = m + n + 1 - (i + j) by omega,
        show m - i + 1 - i = m + 1 - (i + i) by omega,
        show n - j + 1 - j = n + 1 - (j + j) by omega]

/-- **Products of symmetric unimodal polynomials.** Let `P(x) = ∑_{i=0}^{m} aᵢ xⁱ` and
`Q(x) = ∑_{i=0}^{n} bᵢ xⁱ` have nonnegative coefficients, and let `(a₀, …, aₘ)` and
`(b₀, …, bₙ)` be symmetric (`aᵢ = a_{m-i}`, `bᵢ = b_{n-i}`) and unimodal. Then the coefficient
sequence `(c₀, …, c_{m+n})` of `P(x) Q(x)` is symmetric, unimodal and nonnegative (Stanley,
*Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, Chapter 1,
Exercise 50(c)). -/
public theorem symmetric_unimodal_mul {P Q : ℝ[X]} {m n : ℕ} (hPm : P.natDegree ≤ m)
    (hQn : Q.natDegree ≤ n) (hPnn : ∀ i, 0 ≤ P.coeff i) (hQnn : ∀ i, 0 ≤ Q.coeff i)
    (hPsymm : ∀ i ≤ m, P.coeff i = P.coeff (m - i))
    (hQsymm : ∀ i ≤ n, Q.coeff i = Q.coeff (n - i))
    (hPuni : IsUnimodal P.coeff m) (hQuni : IsUnimodal Q.coeff n) :
    (∀ i, 0 ≤ (P * Q).coeff i) ∧
      (∀ i ≤ m + n, (P * Q).coeff i = (P * Q).coeff (m + n - i)) ∧
      IsUnimodal (P * Q).coeff (m + n) := by
  have hexpand := coeff_mul_layers hPm hQn hPsymm hQsymm
  have hsym : ∀ k ≤ m + n, (P * Q).coeff k = (P * Q).coeff (m + n - k) := by
    intro k hk
    rw [hexpand, hexpand]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have h : trapezoid m n i j k = trapezoid m n i j (m + n - k) := by
      unfold trapezoid
      omega
    rw [h]
  refine ⟨fun k => ?_, hsym, unimodal_of_left_half hsym fun k hk => ?_⟩
  · rw [coeff_mul]
    exact sum_nonneg fun ij _ => mul_nonneg (hPnn ij.1) (hQnn ij.2)
  · rw [hexpand, hexpand]
    refine sum_le_sum fun i hi => sum_le_sum fun j hj => ?_
    rw [mem_range] at hi hj
    apply mul_le_mul_of_nonneg_left
    · have h : trapezoid m n i j k ≤ trapezoid m n i j (k + 1) := by
        unfold trapezoid
        omega
      exact_mod_cast h
    · exact mul_nonneg
        (layerWeight_nonneg (hPnn 0) (left_half_mono hPsymm hPuni) (by omega))
        (layerWeight_nonneg (hQnn 0) (left_half_mono hQsymm hQuni) (by omega))

end MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted
