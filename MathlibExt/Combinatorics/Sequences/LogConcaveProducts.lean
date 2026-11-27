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
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# Products of log-concave polynomials

`logConcave_mul` shows that nonnegative coefficients, log-concavity and the absence of internal
zeros are preserved by polynomial multiplication. The proof uses the two-by-two minors of the
Toeplitz matrices of the coefficient sequences.
-/

open Finset Polynomial MathlibExt.Combinatorics.Sequences.Unimodal

namespace MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted

-- Chain inequalities between consecutive translates across the interval from i to j.
private lemma cross_of_succ {a : ℕ → ℝ} (hnn : ∀ i, 0 ≤ a i)
    (hbetween : ∀ i j k, i ≤ j → j ≤ k → a i ≠ 0 → a k ≠ 0 → 0 < a j)
    {d : ℕ} (hstep : ∀ i, a i * a (i + 1 + d) ≤ a (i + d) * a (i + 1))
    {i j : ℕ} (hij : i ≤ j) : a i * a (j + d) ≤ a (i + d) * a j := by
  induction j, hij using Nat.le_induction with
  | base => exact le_of_eq (mul_comm ..)
  | succ j hij ih =>
    by_cases hi : a i = 0
    · simpa [hi] using mul_nonneg (hnn (i + d)) (hnn (j + 1))
    by_cases hk : a (j + 1 + d) = 0
    · simpa [hk] using mul_nonneg (hnn (i + d)) (hnn (j + 1))
    apply le_of_mul_le_mul_right _ (hbetween i j (j + 1 + d) hij (by omega) hi hk)
    calc
      a i * a (j + 1 + d) * a j = a i * (a j * a (j + 1 + d)) := by ring
      _ ≤ a i * (a (j + d) * a (j + 1)) := mul_le_mul_of_nonneg_left (hstep j) (hnn i)
      _ = (a i * a (j + d)) * a (j + 1) := (mul_assoc ..).symm
      _ ≤ (a (i + d) * a j) * a (j + 1) := mul_le_mul_of_nonneg_right ih (hnn _)
      _ = _ := by ring

-- First chain adjacent log-concavity inequalities, then chain the resulting wider ones.
private lemma coeff_cross {P : ℝ[X]} (hnn : ∀ i, 0 ≤ P.coeff i)
    (hlc : IsLogConcave P.coeff P.natDegree) (hnz : NoInternalZeros P.coeff P.natDegree)
    {i j : ℕ} (hij : i ≤ j) (d : ℕ) :
    P.coeff i * P.coeff (j + d) ≤ P.coeff (i + d) * P.coeff j := by
  have between i j k (hij : i ≤ j) (hjk : j ≤ k) (hi : P.coeff i ≠ 0) (hk : P.coeff k ≠ 0) :
      0 < P.coeff j := by
    apply lt_of_le_of_ne (hnn j)
    rcases hij.eq_or_lt with rfl | hij
    · exact hi.symm
    rcases hjk.eq_or_lt with rfl | hjk
    · exact hk.symm
    exact (hnz i j k hij hjk (le_natDegree_of_ne_zero hk) hi hk).symm
  have adjacent k : P.coeff k * P.coeff (k + 1 + 1) ≤ P.coeff (k + 1) * P.coeff (k + 1) := by
    by_cases hk : k + 2 ≤ P.natDegree
    · simpa [pow_two] using hlc k hk
    rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk), mul_zero]
    exact mul_self_nonneg _
  apply cross_of_succ hnn between _ hij
  intro k
  simpa only [Nat.add_right_comm k 1 d, mul_comm (P.coeff (k + 1))] using
    cross_of_succ hnn between adjacent (Nat.le_add_right k d)

-- Row r of the upper triangular Toeplitz matrix is the coefficient sequence shifted by r.
private noncomputable def toeplitz (P : ℝ[X]) (r s : ℕ) : ℝ := (P * X ^ r).coeff s

private lemma toeplitz_nonneg {P : ℝ[X]} (hnn : ∀ i, 0 ≤ P.coeff i) (r s : ℕ) :
    0 ≤ toeplitz P r s := by
  simp only [toeplitz, coeff_mul_X_pow']
  split_ifs <;> simp [hnn]

private lemma toeplitz_minor {P : ℝ[X]} (hnn : ∀ i, 0 ≤ P.coeff i)
    (hlc : IsLogConcave P.coeff P.natDegree) (hnz : NoInternalZeros P.coeff P.natDegree)
    {r r' s t : ℕ} (hr : r ≤ r') (hs : s ≤ t) :
    toeplitz P r t * toeplitz P r' s ≤ toeplitz P r s * toeplitz P r' t := by
  by_cases h : r' ≤ s
  · simp only [toeplitz, coeff_mul_X_pow', ite_eq_left (hr.trans (h.trans hs)), ite_eq_left h,
      ite_eq_left (hr.trans h), ite_eq_left (h.trans hs)]
    rw [mul_comm (P.coeff (t - r))]
    convert coeff_cross hnn hlc hnz (Nat.sub_le_sub_right hs r') (r' - r) using 2 <;>
      congr 1 <;> omega
  · rw [show toeplitz P r' s = 0 by simp [toeplitz, coeff_mul_X_pow', h], mul_zero]
    exact mul_nonneg (toeplitz_nonneg hnn ..) (toeplitz_nonneg hnn ..)

-- A coefficient of the product is the dot product of a shifted row and column.
private lemma toeplitz_mul (P Q : ℝ[X]) (r s N : ℕ) (hs : s < N) :
    toeplitz (P * Q) r s = ∑ k ∈ range N, toeplitz P r k * toeplitz Q k s := by
  calc
    toeplitz (P * Q) r s = ((P * X ^ r) * Q).coeff s := by simp [toeplitz, mul_right_comm]
    _ = ∑ k ∈ range (s + 1), toeplitz P r k * Q.coeff (s - k) := by
      rw [coeff_mul]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (P * X ^ r).coeff i * Q.coeff j) s
    _ = ∑ k ∈ range (s + 1), toeplitz P r k * toeplitz Q k s := by
      apply sum_congr rfl
      intro k hk
      simp [toeplitz, coeff_mul_X_pow', Nat.le_of_lt_succ (mem_range.mp hk)]
    _ = _ := by
      apply sum_subset (range_mono hs)
      intro k _ hk
      have : ¬ k ≤ s := by simpa [Nat.lt_succ_iff] using hk
      simp [toeplitz, coeff_mul_X_pow', this]

-- The two-by-two Cauchy–Binet identity, summing over both orders of each pair of indices.
private lemma sum_minor (S : Finset ℕ) (a b c d : ℕ → ℝ)
    (hab : ∀ i j, i ≤ j → a j * b i ≤ a i * b j)
    (hcd : ∀ i j, i ≤ j → c j * d i ≤ c i * d j) :
    (∑ i ∈ S, a i * d i) * (∑ i ∈ S, b i * c i) ≤
      (∑ i ∈ S, a i * c i) * (∑ i ∈ S, b i * d i) := by
  have pair i j : 0 ≤ (a i * b j - a j * b i) * (c i * d j - c j * d i) := by
    rcases le_total i j with h | h
    · exact mul_nonneg (sub_nonneg.mpr (hab i j h)) (sub_nonneg.mpr (hcd i j h))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hab j i h))
        (sub_nonpos.mpr (hcd j i h))
  have expand i j : (a i * b j - a j * b i) * (c i * d j - c j * d i) =
      (a i * c i) * (b j * d j) - (a i * d i) * (b j * c j) -
      (b i * c i) * (a j * d j) + (b i * d i) * (a j * c j) := by ring
  have h := sum_nonneg (s := S) fun i _ => sum_nonneg (s := S) fun j _ => pair i j
  simp only [expand, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul] at h
  linarith

/-- **Products of log-concave polynomials.** Let `P(x)` and `Q(x)` have nonnegative coefficients
and log-concave coefficient sequences with no internal zeros (indexed up to their degrees). Then
the same holds for `P(x) Q(x)` (Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's
draft of 15 July 2011, Chapter 1, Exercise 50(d)). -/
public theorem logConcave_mul {P Q : ℝ[X]} (hPnn : ∀ i, 0 ≤ P.coeff i)
    (hQnn : ∀ i, 0 ≤ Q.coeff i)
    (hPlc : IsLogConcave P.coeff P.natDegree) (hQlc : IsLogConcave Q.coeff Q.natDegree)
    (hPnz : NoInternalZeros P.coeff P.natDegree) (hQnz : NoInternalZeros Q.coeff Q.natDegree) :
    (∀ i, 0 ≤ (P * Q).coeff i) ∧ IsLogConcave (P * Q).coeff (P * Q).natDegree ∧
      NoInternalZeros (P * Q).coeff (P * Q).natDegree := by
  have nonneg i : 0 ≤ (P * Q).coeff i := by
    rw [coeff_mul]
    exact sum_nonneg fun x _ => mul_nonneg (hPnn x.1) (hQnn x.2)
  have minor {r r' s t : ℕ} (hr : r ≤ r') (hs : s ≤ t) :
      toeplitz (P * Q) r t * toeplitz (P * Q) r' s ≤
        toeplitz (P * Q) r s * toeplitz (P * Q) r' t := by
    have ht : t < t + 1 := Nat.lt_succ_self t
    simp only [toeplitz_mul P Q _ t _ ht, toeplitz_mul P Q _ s _ (hs.trans_lt ht)]
    apply sum_minor
    · exact fun i j hij => toeplitz_minor hPnn hPlc hPnz hr hij
    · intro i j hij
      simpa only [mul_comm (toeplitz Q j s)] using toeplitz_minor hQnn hQlc hQnz hij hs
  have cross (i j d : ℕ) (hij : i ≤ j) :
      (P * Q).coeff i * (P * Q).coeff (j + d) ≤ (P * Q).coeff (i + d) * (P * Q).coeff j := by
    have h := minor (Nat.zero_le d) (Nat.add_le_add_right hij d)
    simpa [toeplitz, mul_comm ((P * Q).coeff i)] using h
  refine ⟨nonneg, fun k _ => ?_, fun i j k hij hjk _ hi hk => ?_⟩
  · simpa only [pow_two] using cross k (k + 1) 1 (Nat.le_succ k)
  · have h := cross i (k - (j - i)) (j - i) (by omega)
    rw [show k - (j - i) + (j - i) = k by omega, show i + (j - i) = j by omega] at h
    intro hj
    rw [hj, zero_mul] at h
    exact (mul_pos ((nonneg i).lt_of_ne hi.symm) ((nonneg k).lt_of_ne hk.symm)).not_ge h

end MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted
