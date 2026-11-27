/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Alternating binomial sums

These identities are from Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, [INTEGERS 26 (2026), Article A32](https://math.colgate.edu/~integers/aa32/aa32.pdf),
Lemma 3, equations (2)–(4). The lemma explicitly assumes `m, n ∈ ℕ`, without requiring `m ≤ n`,
and uses binomial reflection. Here the upper indices of shifted coefficients are integers
throughout, including outside the range of the paper's factorial calculations. We make `k : ℕ`
and `j ≤ m` in (2) explicit, and in (4) set the summand to zero for `j > k`.
-/

namespace MetaMathlibExt

open Finset

private theorem neg_one_pow_mul_ringChoose (x : ℤ) (r : ℕ) :
    (-1 : ℤ) ^ r * Ring.choose x r = Ring.choose ((r : ℤ) - x - 1) r := by
  rw [show (r : ℤ) - x - 1 = -(x + 1 - r) by ring, Ring.choose_neg, Units.smul_def,
    zsmul_eq_mul, Int.cast_id, Int.coe_negOnePow_natCast, show x + 1 - (r : ℤ) + r - 1 = x by ring]

private theorem alternating_weight_eq (m n j : ℕ) (hj : j ≤ m) :
    (-1 : ℤ) ^ (m - j) * Ring.choose (n : ℤ) j * Ring.choose ((n : ℤ) - j - 1) (m - j) =
      Ring.choose (n : ℤ) j * Ring.choose ((m : ℤ) - n) (m - j) := by
  rw [mul_right_comm, neg_one_pow_mul_ringChoose,
    show ((m - j : ℕ) : ℤ) - ((n : ℤ) - j - 1) - 1 = (m : ℤ) - n by omega, mul_comm]

-- Generalized absorption keeps the shifted upper index in ℤ, even when it is negative.
private theorem choose_mul_choose_sub (x : ℤ) {a b : ℕ} (h : b ≤ a) :
    Ring.choose x a * Ring.choose (a : ℤ) b = Ring.choose x b * Ring.choose (x - b) (a - b) := by
  rw [Ring.choose_natCast, mul_comm, ← nsmul_eq_mul, Ring.choose_smul_choose x h]

private theorem choose_mul_choose_swap (x : ℤ) (j k : ℕ) :
    Ring.choose x j * Ring.choose (x - j) k = Ring.choose x k * Ring.choose (x - k) j := by
  calc
    _ = Ring.choose x (j + k) * Ring.choose (↑(j + k) : ℤ) j := by
      rw [choose_mul_choose_sub x (Nat.le_add_right j k), Nat.add_sub_cancel_left]
    _ = Ring.choose x (j + k) * Ring.choose (↑(j + k) : ℤ) k := by
      rw [Ring.choose_natCast, Ring.choose_natCast, Nat.choose_symm_add]
    _ = _ := by rw [choose_mul_choose_sub x (Nat.le_add_left k j), Nat.add_sub_cancel]

private theorem sum_range_choose_mul (x y : ℤ) (r : ℕ) :
    ∑ j ∈ range (r + 1), Ring.choose x j * Ring.choose y (r - j) = Ring.choose (x + y) r := by
  rw [Ring.add_choose_eq r (Commute.all x y), Nat.sum_antidiagonal_eq_sum_range_succ_mk]

-- Pascal's recurrence cancels consecutive terms even when the upper index is negative.
private theorem sum_range_alternating_choose (x : ℤ) (r : ℕ) :
    ∑ s ∈ range (r + 1), (-1 : ℤ) ^ s * Ring.choose (x + 1) s =
      (-1 : ℤ) ^ r * Ring.choose x r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [sum_range_succ, ih, Ring.choose_succ_succ, pow_succ, mul_add]
      ring

private theorem sum_Icc_alternating_choose (m n j : ℕ) (hj : j ≤ m) :
    ∑ s ∈ Icc j m, (-1 : ℤ) ^ (s - j) * Ring.choose (n : ℤ) s * Ring.choose (s : ℤ) j =
      (-1 : ℤ) ^ (m - j) * Ring.choose (n : ℤ) j * Ring.choose ((n : ℤ) - j - 1) (m - j) := by
  calc
    _ = ∑ s ∈ Icc j m, Ring.choose (n : ℤ) j *
        ((-1 : ℤ) ^ (s - j) * Ring.choose ((n : ℤ) - j) (s - j)) := by
      refine sum_congr rfl fun s hs ↦ ?_
      rw [mul_assoc, choose_mul_choose_sub (n : ℤ) (mem_Icc.mp hs).1, mul_left_comm]
    _ = Ring.choose (n : ℤ) j *
        ∑ s ∈ range (m - j + 1), (-1 : ℤ) ^ s * Ring.choose ((n : ℤ) - j) s := by
      have hI : Icc j m = Ico j (m + 1) := by
        ext s
        simp only [mem_Icc, mem_Ico]
        omega
      rw [← mul_sum, hI, sum_Ico_eq_sum_range, show m + 1 - j = m - j + 1 by omega]
      simp only [Nat.add_sub_cancel_left]
    _ = _ := by
      have h := sum_range_alternating_choose ((n : ℤ) - j - 1) (m - j)
      rw [sub_add_cancel] at h
      rw [h, mul_left_comm, ← mul_assoc]

/-- **Alternating binomial sum identities.** For an integer $x$ and a natural number $r$ write
$\binom{x}{r} = x(x-1)\cdots(x-r+1)/r!$ for the generalized binomial coefficient. Let $m$, $n$
and $k$ be natural numbers. Then for every natural number $j \le m$,
$$\sum_{s=j}^{m} (-1)^{s-j} \binom{n}{s} \binom{s}{j} = (-1)^{m-j} \binom{n}{j} \binom{n-j-1}{m-j}
= \binom{n}{j} \binom{m-n}{m-j},$$
and
$$\sum_{j=0}^{m} (-1)^{m-j} \binom{n}{j} \binom{n-j-1}{m-j} \binom{n-j}{k} =
\binom{n}{k} \binom{m-k}{m},$$
$$\sum_{j=0}^{\min(m, k)} (-1)^{m-j} \binom{n}{j} \binom{n-j-1}{m-j} \binom{n-j}{k-j} =
\binom{n}{k} \binom{k+m-n}{m}.$$

Source: Walid Kehila, *An Extension of Wolstenholme's Theorem by Binomial
Coefficients*, INTEGERS 26 (2026), Article A32, Lemma 3
(`integers-2026-A32-lem-3`). -/
public theorem alternating_choose_sum_identities (m n k : ℕ) :
    let C : ℤ → ℕ → ℤ := fun x r => Ring.choose x r
    (∀ j ≤ m, ∑ s ∈ Finset.Icc j m, (-1 : ℤ) ^ (s - j) * C n s * C s j =
          (-1) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) ∧
        (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) =
          C n j * C ((m : ℤ) - n) (m - j)) ∧
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) * C ((n : ℤ) - j) k =
        C n k * C ((m : ℤ) - k) m ∧
      ∑ j ∈ Finset.range (m + 1),
          (-1 : ℤ) ^ (m - j) * C n j * C ((n : ℤ) - j - 1) (m - j) *
            (if j ≤ k then C ((n : ℤ) - j) (k - j) else 0) =
        C n k * C ((k : ℤ) + m - n) m := by
  dsimp only
  refine ⟨fun j hj ↦ ⟨sum_Icc_alternating_choose m n j hj, alternating_weight_eq m n j hj⟩,
    ?_, ?_⟩
  · calc
      _ = ∑ j ∈ range (m + 1), Ring.choose (n : ℤ) k *
          (Ring.choose ((n : ℤ) - k) j * Ring.choose ((m : ℤ) - n) (m - j)) := by
        refine sum_congr rfl fun j hj ↦ ?_
        rw [alternating_weight_eq m n j (Nat.lt_succ_iff.mp (mem_range.mp hj)),
          mul_right_comm, choose_mul_choose_swap, mul_assoc]
      _ = _ := by
        rw [← mul_sum, sum_range_choose_mul, show (n : ℤ) - k + (m - n) = m - k by ring]
  · calc
      _ = ∑ j ∈ range (m + 1), Ring.choose (n : ℤ) k *
          (Ring.choose (k : ℤ) j * Ring.choose ((m : ℤ) - n) (m - j)) := by
        refine sum_congr rfl fun j hj ↦ ?_
        rw [alternating_weight_eq m n j (Nat.lt_succ_iff.mp (mem_range.mp hj)), mul_right_comm]
        by_cases hjk : j ≤ k
        · rw [ite_eq_left hjk, ← choose_mul_choose_sub (n : ℤ) hjk, mul_assoc]
        · have hzero : k.choose j = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hjk)
          simp [hjk, Ring.choose_natCast, hzero]
      _ = _ := by
        rw [← mul_sum, sum_range_choose_mul, show (k : ℤ) + (m - n) = k + m - n by ring]

end MetaMathlibExt
