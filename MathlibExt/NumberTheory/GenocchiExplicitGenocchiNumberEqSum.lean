/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GenocchiNumber
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Order.Interval.Finset.Nat
import MathlibExt.NumberTheory.GenocchiExplicit
import MathlibExt.NumberTheory.GenocchiBernoulli
import MathlibExt.Combinatorics.Enumerative.GarabedianBernoulliStirling
import Mathlib.Tactic.Ring

/-!
# Explicit formula for Genocchi numbers via Stirling numbers

The Genocchi numbers equal the Zerroukhat–Khaldi double sum of Stirling numbers.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas for Bernoulli
and Genocchi Numbers", Journal of Integer Sequences 28 (2025), Article 25.6.7, Theorem 1.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.GenocchiExplicitWanted

private theorem sum_stirlingSecond_succ (m : ℕ) (f : ℕ → ℚ) :
    ∑ k ∈ Finset.range (m + 1 + 1), f k * Nat.stirlingSecond (m + 1) k =
      ∑ k ∈ Finset.range (m + 1), (f k * k + f (k + 1)) * Nat.stirlingSecond m k := by
  have shift :
      ∑ k ∈ Finset.range (m + 1), f (k + 1) * (k + 1 : ℕ) * Nat.stirlingSecond m (k + 1) =
        ∑ k ∈ Finset.range (m + 1), f k * k * Nat.stirlingSecond m k := by
    rw [Finset.sum_range_succ _ m,
      Finset.sum_range_succ' (fun k ↦ f k * k * Nat.stirlingSecond m k)]
    simp [Nat.stirlingSecond_eq_zero_of_lt m.lt_succ_self]
  rw [Finset.sum_range_succ' _ (m + 1)]
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero,
    Nat.stirlingSecond_succ_succ, Nat.cast_add _ (Nat.stirlingSecond m _), Nat.cast_mul]
  simp only [mul_add, add_mul, ← mul_assoc, Finset.sum_add_distrib, shift]

private theorem sum_zerroU_eq_base (r m : ℕ) (hm : 0 < m) :
    ∑ k ∈ Finset.range (m + 1), zerroU r k * (Nat.stirlingSecond m k : ℚ) =
      ∑ k ∈ Finset.range (m + r + 1), zerroU 0 k *
        (Nat.stirlingSecond (m + r) k : ℚ) := by
  induction r generalizing m with
  | zero => simp
  | succ r ih =>
    rw [show m + (r + 1) = (m + 1) + r by omega, ← ih (m + 1) (by omega)]
    rw [sum_stirlingSecond_succ]
    apply Finset.sum_congr rfl
    intro k _
    cases k with
    | zero =>
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      simp
    | succ k =>
      rw [zerroU_succ r (k + 1) (by omega)]
      ring

private theorem sum_zerroU_base (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), zerroU 0 k * (Nat.stirlingSecond n k : ℚ) =
      (-1 : ℚ) ^ n * ∑ k ∈ Finset.Icc 1 n,
        ((-1 : ℚ) ^ (n - k) * (k - 1).factorial * Nat.stirlingSecond n k) /
          2 ^ (k - 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr_of_eq_on_inter
  · intro k hk hkn
    have hk0 : k = 0 := by
      simp only [Finset.mem_range, Finset.mem_Icc] at hk hkn
      omega
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [hk0]
  · intro k hk hkn
    simp only [Finset.mem_range, Finset.mem_Icc] at hk hkn
    omega
  · intro k _ hk
    have hk' := (Finset.mem_Icc.mp hk).2
    have hsign : (-1 : ℚ) ^ n * (-1) ^ (n - k) = (-1) ^ k := by
      rw [← pow_add, show n + (n - k) = 2 * (n - k) + k by omega, pow_add, pow_mul]
      simp
    simp only [zerroU, zero_add, add_zero, Finset.sum_range_one,
      Nat.stirlingSecond_zero, Nat.cast_one, mul_one]
    rw [← hsign]
    ring

/-- **Explicit formula for Genocchi numbers via Stirling numbers.** Let $n$ and $r$ be positive
integers with $n \ge r + 1$, let $G_n$ be the $n$-th Genocchi number and let $S(a, b)$ denote
the Stirling numbers of the second kind. For $k \ge 1$ write
$c_k = \sum_{j=0}^{r} (-1)^{k+j+r} \frac{(k+j-1)!}{2^{k+j-1}} S(r, j)$. Then
$G_n = (-1)^n \, n \sum_{k=1}^{n-r} c_k \, S(n-r, k)$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Theorem 1. -/
theorem genocchiNumber_eq_sum (n r : ℕ) (hn : 1 ≤ n)
    (hr : 1 ≤ r) (hnr : r + 1 ≤ n) :
    MetaMathlibExt.genocchiNumber n =
      (-1 : ℚ) ^ n * (n : ℚ) *
        ∑ k ∈ Finset.Icc 1 (n - r),
          (∑ j ∈ Finset.range (r + 1),
            (-1 : ℚ) ^ (k + j + r) *
              ((k + j - 1).factorial : ℚ) / 2 ^ (k + j - 1) *
              (Nat.stirlingSecond r j : ℚ)) *
          (Nat.stirlingSecond (n - r) k : ℚ) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le' hr
  have hrow := sum_zerroU_eq_base (r + 1) (n - (r + 1)) (by omega)
  rw [Nat.sub_add_cancel (by omega : (r + 1) ≤ n), sum_zerroU_base n hn] at hrow
  have hIcc : (∑ k ∈ Finset.Icc 1 (n - (r + 1)), zerroU (r + 1) k *
      (Nat.stirlingSecond (n - (r + 1)) k : ℚ)) =
      ∑ k ∈ Finset.range (n - (r + 1) + 1), zerroU (r + 1) k *
        (Nat.stirlingSecond (n - (r + 1)) k : ℚ) := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk hk'
      have hk0 : k = 0 := by
        simp only [Finset.mem_Icc, Finset.mem_range] at hk hk'
        omega
      obtain ⟨m, hm⟩ : ∃ m, n - (r + 1) = m + 1 := ⟨n - (r + 1) - 1, by omega⟩
      simp [hk0, hm]
  change MetaMathlibExt.genocchiNumber n = (-1 : ℚ) ^ n * (n : ℚ) *
    ∑ k ∈ Finset.Icc 1 (n - (r + 1)), zerroU (r + 1) k * (Nat.stirlingSecond (n - (r + 1)) k : ℚ)
  rw [hIcc, hrow, MetaMathlibExt.genocchiNumber_eq_bernoulli,
    MetaMathlibExt.garabedian_genocchi_formula_general]
  have hsign : (-1 : ℚ) ^ n * (-1 : ℚ) ^ n = 1 := by
    rw [← pow_add, ← two_mul n, pow_mul]
    simp
  rw [← mul_assoc, mul_right_comm ((-1 : ℚ) ^ n) (n : ℚ), mul_assoc,
    hsign, one_mul]

end MathlibExt.NumberTheory.GenocchiExplicitWanted
