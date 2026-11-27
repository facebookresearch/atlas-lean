/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.KFibonacciBinomialTruncation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Recurrence for the truncated binomial sums

We align the truncation ranges in Farhi's Proposition 11 and apply Pascal's identity
for integer upper arguments. The proof does not use any Fibonacci sequence.
-/

namespace MetaMathlibExt

private def binomialDiff (a : ℤ) (i : ℕ) : ℤ :=
  Ring.choose a i - if i = 0 then 0 else Ring.choose a (i - 1)

private def weightedBinomialDiff (d m i : ℕ) : ℚ :=
  (binomialDiff ((d * i : ℕ) - (m : ℤ)) i : ℚ) / 2 ^ (d * i)

private theorem weightedBinomialDiff_zero (d m : ℕ) : weightedBinomialDiff d m 0 = 1 := by
  simp [weightedBinomialDiff, binomialDiff]

-- At index 1 the shifted difference contains a lower index of −1, hence just `choose a 0`.
private theorem binomialDiff_pascal (a : ℤ) (i : ℕ) :
    binomialDiff (a + 1) (i + 1) - binomialDiff a (i + 1) = binomialDiff a i := by
  cases i with
  | zero => simp [binomialDiff]
  | succ i =>
    simp only [binomialDiff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [Ring.choose_succ_succ a (i + 1), Ring.choose_succ_succ a i]
    ring

private theorem weightedBinomialDiff_shift (k n i : ℕ) :
    weightedBinomialDiff (k + 1) (n + k) (i + 1) -
        weightedBinomialDiff (k + 1) (n + k + 1) (i + 1) =
      weightedBinomialDiff (k + 1) n i / (2 : ℚ) ^ (k + 1) := by
  let a : ℤ := ((k + 1) * i : ℕ) - (n : ℤ)
  have h₁ : (((k + 1) * (i + 1) : ℕ) : ℤ) - ((n + k + 1 : ℕ) : ℤ) = a := by
    simp only [a, Nat.mul_succ, Nat.cast_add, Nat.cast_one]
    ring
  have h₂ : (((k + 1) * (i + 1) : ℕ) : ℤ) - ((n + k : ℕ) : ℤ) = a + 1 := by
    simp only [Nat.cast_add, Nat.cast_one] at h₁ ⊢
    omega
  rw [weightedBinomialDiff, weightedBinomialDiff, weightedBinomialDiff, h₁, h₂,
    div_sub_div_same, ← Int.cast_sub, binomialDiff_pascal]
  rw [Nat.mul_succ, pow_add, div_div]

-- The cutoff moves by one exactly when `k + 1` divides `n + k`. The new term has
-- upper argument 0 and both lower arguments are positive, so it contributes nothing.
private theorem sum_weightedBinomialDiff_extend (k n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.range ((n + k - 1) / (k + 1) + 1), weightedBinomialDiff (k + 1) (n + k) i =
      ∑ i ∈ Finset.range ((n + k) / (k + 1) + 1), weightedBinomialDiff (k + 1) (n + k) i := by
  have hcut := Nat.succ_div (a := n + k - 1) (b := k + 1)
  rw [show n + k - 1 + 1 = n + k by omega] at hcut
  by_cases h : k + 1 ∣ n + k
  · rw [ite_eq_left h] at hcut
    have htop : (k + 1) * ((n + k) / (k + 1)) = n + k := by
      simpa [Nat.mod_eq_zero_of_dvd h] using Nat.div_add_mod (n + k) (k + 1)
    have hidx : 2 ≤ (n + k) / (k + 1) := by
      have hpos : 1 ≤ (n + k - 1) / (k + 1) :=
        (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
      omega
    have hzero : weightedBinomialDiff (k + 1) (n + k) ((n + k) / (k + 1)) = 0 := by
      simp [weightedBinomialDiff, binomialDiff, htop,
        Ring.choose_zero_pos ℤ (by omega : 0 < (n + k) / (k + 1)),
        Ring.choose_zero_pos ℤ (by omega : 0 < (n + k) / (k + 1) - 1)]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [hzero, add_zero, hcut]
  · rw [ite_eq_right h, add_zero] at hcut
    rw [hcut]

/-- **Recurrence for the truncated binomial sums.** Let $G_n^{(k)}$ be the truncated binomial
sum. For all natural numbers $k \ge 2$ and $n \ge 2$,
$G_{n+k+1}^{(k)} = 2 G_{n+k}^{(k)} - G_n^{(k)}$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Proposition 11 (`jis-2024-24.1.1-prop-11`). -/
public theorem kFibonacciBinomialTruncation_recurrence (k n : ℕ) (hk : 2 ≤ k)
    (hn : 2 ≤ n) :
    kFibonacciBinomialTruncation k (n + k + 1) =
      2 * kFibonacciBinomialTruncation k (n + k) - kFibonacciBinomialTruncation k n := by
  let q := (n + k) / (k + 1)
  have hq : q = (n - 1) / (k + 1) + 1 := by
    dsimp [q]
    rw [show n + k = (n - 1) + (k + 1) by omega, Nat.add_div_right _ (by omega)]
  -- Split at zero before shifting, since the difference of the two terms there is zero.
  have hs :
      (∑ i ∈ Finset.range (q + 1), weightedBinomialDiff (k + 1) (n + k) i) -
          (∑ i ∈ Finset.range (q + 1), weightedBinomialDiff (k + 1) (n + k + 1) i) =
        (∑ i ∈ Finset.range q, weightedBinomialDiff (k + 1) n i) / (2 : ℚ) ^ (k + 1) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_range_succ']
    simp only [weightedBinomialDiff_zero, sub_self, add_zero, weightedBinomialDiff_shift]
    simp only [div_eq_mul_inv, Finset.sum_mul]
  have hp (m : ℕ) : kFibonacciBinomialTruncation k m = (2 : ℚ) ^ ((m : ℤ) - 2) *
      ∑ i ∈ Finset.range ((m - 1) / (k + 1) + 1), weightedBinomialDiff (k + 1) m i := rfl
  have hpow : (2 : ℚ) ^ (((n + k + 1 : ℕ) : ℤ) - 2) =
      2 * (2 : ℚ) ^ (((n + k : ℕ) : ℤ) - 2) := by
    rw [show (((n + k + 1 : ℕ) : ℤ) - 2) = (((n + k : ℕ) : ℤ) - 2) + 1 by omega,
      zpow_add₀ (by norm_num), zpow_one, mul_comm]
  have hshift : (2 : ℚ) ^ (((n + k + 1 : ℕ) : ℤ) - 2) =
      (2 : ℚ) ^ ((n : ℤ) - 2) * (2 : ℚ) ^ (k + 1) := by
    rw [show (((n + k + 1 : ℕ) : ℤ) - 2) = ((n : ℤ) - 2) + ((k + 1 : ℕ) : ℤ) by omega,
      zpow_add₀ (by norm_num), zpow_natCast]
  let A := (2 : ℚ) ^ (((n + k + 1 : ℕ) : ℤ) - 2)
  have hscaled : A *
        ((∑ i ∈ Finset.range (q + 1), weightedBinomialDiff (k + 1) (n + k) i) -
          ∑ i ∈ Finset.range (q + 1), weightedBinomialDiff (k + 1) (n + k + 1) i) =
      (2 : ℚ) ^ ((n : ℤ) - 2) * ∑ i ∈ Finset.range q, weightedBinomialDiff (k + 1) n i := by
    rw [hs, show A = _ from hshift]
    field_simp
  rw [hp, hp, hp, show n + k + 1 - 1 = n + k by omega, sum_weightedBinomialDiff_extend k n hn,
    ← hq, ← mul_assoc, ← hpow, ← hscaled, mul_sub, sub_sub_cancel]

end MetaMathlibExt
