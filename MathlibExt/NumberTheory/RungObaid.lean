/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The Rung-Obaid trigonometric identity

The binomial-weighted sum of multiple-angle sines is evaluated by showing that it and
the closed form satisfy Pascal's recurrence with the same boundary values.
-/

namespace MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted

open Finset

-- The contribution from the horizontal axis of Pascal's recurrence.
private noncomputable def boundarySum (f : ℕ → ℝ) (n : ℕ) : ℕ → ℝ
  | 0 => f n
  | k + 1 => ∑ i ∈ Icc 1 n, ((n + k - i).choose k : ℝ) * f i

private lemma boundarySum_succ (f : ℕ → ℝ) (n k : ℕ) :
    boundarySum f (n + 1) (k + 1) = boundarySum f (n + 1) k + boundarySum f n (k + 1) := by
  cases k with
  | zero => simp [boundarySum, sum_Icc_succ_top (Nat.succ_pos n), add_comm]
  | succ k =>
    simp only [boundarySum, sum_Icc_succ_top (Nat.succ_pos n)]
    have hlast (j : ℕ) : n + 1 + j - (n + 1) = j := by omega
    simp only [hlast, Nat.choose_self, Nat.cast_one, one_mul]
    rw [add_right_comm _ (f (n + 1)), ← sum_add_distrib]
    congr 1
    apply sum_congr rfl
    intro i hi
    have hi' := (mem_Icc.mp hi).2
    rw [show n + 1 + (k + 1) - i = (n + 1 + k - i) + 1 by omega,
      Nat.choose_succ_succ', Nat.cast_add, add_mul]
    rw [show n + 1 + k - i = n + (k + 1) - i by omega]

private noncomputable def sineTerm (θ : ℝ) (n k : ℕ) : ℝ :=
  (2 * Real.cos θ) ^ (n + k) * Real.sin (((n : ℝ) - k) * θ)

private lemma sineTerm_succ (θ : ℝ) (n k : ℕ) :
    sineTerm θ (n + 1) (k + 1) = sineTerm θ (n + 1) k + sineTerm θ n (k + 1) := by
  unfold sineTerm
  rw [show n + 1 + k = n + k + 1 by omega, Nat.add_succ n k,
    show n + 1 + (k + 1) = (n + k + 1) + 1 by omega, pow_succ _ (n + k + 1)]
  simp only [Nat.cast_succ, ← mul_add, Real.sin_add_sin]
  ring_nf

private lemma sineTerm_eq (θ : ℝ) (n k : ℕ) :
    sineTerm θ n k =
      boundarySum (fun i => sineTerm θ i 0) n k - boundarySum (fun i => sineTerm θ i 0) k n := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [boundarySum, sineTerm]
    | succ k =>
      simp only [boundarySum, Icc_eq_empty_of_lt Nat.zero_lt_one, sum_empty, sineTerm,
        Nat.zero_add, Nat.add_zero, Nat.cast_zero, zero_sub, sub_zero, neg_mul, Real.sin_neg,
        mul_neg]
  | succ n ih =>
    induction k with
    | zero => simp [boundarySum]
    | succ k ihk =>
      rw [sineTerm_succ, ihk, ih, boundarySum_succ, boundarySum_succ]
      ring

private lemma boundarySum_of_pos (f : ℕ → ℝ) (n : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    boundarySum f n k = ∑ i ∈ Icc 1 n, ((n + k - i - 1).choose (k - 1) : ℝ) * f i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [boundarySum, Nat.add_one_sub_one]
  apply sum_congr rfl
  intro i _
  rw [show n + (k + 1) - i - 1 = n + k - i by omega]

/-- **The Rung-Obaid trigonometric identity.** Let $k$ and $n$ be natural numbers with
$1 \le k \le n$, and let $\theta$ be a real number. Then

$$\sum_{\nu=1}^{n} 2^\nu \left( \binom{n+k-\nu-1}{k-1} - \binom{n+k-\nu-1}{n-1} \right)
\cos^\nu \theta \, \sin(\nu\theta) = 2^{n+k} \cos^{n+k} \theta \, \sin((n-k)\theta).$$

Source: D. C. Rung and S. A. Obaid, "Combinatorics and flexure", ZAMP 36 (1985),
443–459; stated as Lemma 6 in Horst Alzer and Man Kam Kwong, "Ramanujan and a
Combinatorial Identity Involving Harmonic Numbers", Journal of Integer Sequences 29 (2026),
Article 26.4.8. -/
public theorem sum_two_pow_choose_sub_mul_cos_pow_sin
    (k n : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (θ : ℝ) :
    ∑ ν ∈ Finset.Icc 1 n,
        (2 : ℝ) ^ ν *
          ((Nat.choose (n + k - ν - 1) (k - 1) : ℝ) -
            (Nat.choose (n + k - ν - 1) (n - 1) : ℝ)) *
          Real.cos θ ^ ν * Real.sin ((ν : ℝ) * θ) =
      (2 : ℝ) ^ (n + k) * Real.cos θ ^ (n + k) *
        Real.sin (((n : ℝ) - (k : ℝ)) * θ) := by
  let f (i : ℕ) := sineTerm θ i 0
  let a (i : ℕ) := n + k - i - 1
  have hpad :
      ∑ i ∈ Icc 1 k, ((a i).choose (n - 1) : ℝ) * f i =
        ∑ i ∈ Icc 1 n, ((a i).choose (n - 1) : ℝ) * f i := by
    apply sum_subset (Icc_subset_Icc_right hkn)
    intro i hi hki
    simp only [mem_Icc] at hi hki
    have : a i < n - 1 := by dsimp [a]; omega
    simp [Nat.choose_eq_zero_of_lt this]
  have h := sineTerm_eq θ n k
  rw [boundarySum_of_pos _ _ hk, boundarySum_of_pos _ _ (hk.trans hkn), Nat.add_comm k n] at h
  change sineTerm θ n k = (∑ i ∈ Icc 1 n, ((a i).choose (k - 1) : ℝ) * f i) -
    ∑ i ∈ Icc 1 k, ((a i).choose (n - 1) : ℝ) * f i at h
  rw [hpad, ← sum_sub_distrib] at h
  calc
    _ = ∑ i ∈ Icc 1 n, (((a i).choose (k - 1) : ℝ) * f i -
          ((a i).choose (n - 1) : ℝ) * f i) := by
      apply sum_congr rfl
      intro i _
      simp only [f, a, sineTerm, Nat.add_zero, Nat.cast_zero, sub_zero, mul_pow]
      ring
    _ = sineTerm θ n k := h.symm
    _ = _ := by rw [sineTerm, mul_pow]

end MathlibExt.NumberTheory.RamanujanHarmonicIdentityWanted
