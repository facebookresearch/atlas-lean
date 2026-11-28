/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.TakagiFunction
public import MathlibExt.NumberTheory.Digits.BinaryDigitSum
import Mathlib.Tactic.LinearCombination

/-!
# Hamming weight from consecutive Takagi values

For natural numbers `k` and `r` with `r < 2 ^ k`, the difference of the Takagi values at
`r / 2 ^ k` and `(r + 1) / 2 ^ k` determines the number of ones in the binary expansion of
`2 ^ k + r`. The proof works directly with the coefficient series: appending a zero leaves
its value unchanged, and appending a one changes the last prefix term and the geometric tail.

## References

* Laura Monroe, *Takagi Function Identities on Dyadic Rationals*,
  Journal of Integer Sequences 27 (2024), Article 24.2.7, pp. 1–14, Definition 3,
  Lemma 13 and Theorem 28. Unlike the paper's derivation from Theorem 26, the proof here
  uses the binary coefficients of Definition 3 directly.
-/

namespace MetaMathlibExt

open Finset

private def prefixOnes (n : ℕ) (k : ℤ) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, takagiBit n (k - j)

private theorem takagiBit_of_nonneg (n : ℕ) {j : ℤ} (hj : 0 ≤ j) :
    takagiBit n j = (n.testBit j.toNat).toNat := by
  rw [takagiBit_eq, ite_eq_left hj]
  cases n.testBit j.toNat <;> rfl

private theorem takagiBit_append (n b : ℕ) (hb : b < 2) (j : ℤ) :
    takagiBit (2 * n + b) j = if j = 0 then b else takagiBit n (j - 1) := by
  rcases lt_trichotomy j 0 with h | rfl | h
  · rw [ite_eq_right h.ne, takagiBit_neg _ _ h, takagiBit_neg _ _ (by omega)]
  · rw [ite_eq_left rfl, takagiBit_of_nonneg _ le_rfl, Nat.toNat_testBit]
    simp only [Int.toNat_zero, pow_zero, Nat.div_one]
    omega
  · rw [ite_eq_right h.ne', takagiBit_of_nonneg _ h.le, takagiBit_of_nonneg _ (by omega),
      show j.toNat = (j - 1).toNat + 1 by omega, ← Nat.testBit_div_two,
      show (2 * n + b) / 2 = n by omega]

private theorem prefixOnes_append_of_le (n b k i : ℕ) (hb : b < 2) (hi : i ≤ k) :
    prefixOnes (2 * n + b) k i = prefixOnes n ((k : ℤ) - 1) i := by
  unfold prefixOnes
  apply sum_congr rfl
  intro j hj
  have hjk := mem_range.mp hj
  rw [takagiBit_append n b hb, ite_eq_right (by omega : (k : ℤ) - j ≠ 0), sub_right_comm]

private theorem prefixOnes_append (n b k : ℕ) (hb : b < 2) :
    prefixOnes (2 * n + b) k (k + 1) = prefixOnes n ((k : ℤ) - 1) k + b := by
  rw [show prefixOnes (2 * n + b) k (k + 1) =
      prefixOnes (2 * n + b) k k + takagiBit (2 * n + b) ((k : ℤ) - k) from sum_range_succ ..,
    prefixOnes_append_of_le n b k k hb le_rfl, sub_self, takagiBit_append n b hb, ite_eq_left rfl]

private theorem prefixOnes_eq_digits (k n : ℕ) (hn : n < 2 ^ k) :
    prefixOnes n ((k : ℤ) - 1) k = (Nat.digits 2 n).sum := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simpa using hn
    simp [this, prefixOnes]
  | succ k ih =>
    let u := n / 2
    let b := n % 2
    have hb : b < 2 := Nat.mod_lt _ two_pos
    have hu : u < 2 ^ k := by
      rw [pow_succ] at hn
      omega
    have hn' : n = 2 * u + b := (Nat.div_add_mod n 2).symm
    have hdigits : (Nat.digits 2 (2 * u + b)).sum = (Nat.digits 2 u).sum + b := by
      have h := Nat.sum_digits_ofDigits_eq_sum (b := 2) one_lt_two
        (L := b :: Nat.digits 2 u) (l := (b :: Nat.digits 2 u).length)
        ⟨rfl, fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact Nat.digits_lt_base one_lt_two hx⟩
      simpa only [Nat.ofDigits_cons, Nat.ofDigits_digits, List.sum_cons, add_comm] using h
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = k by omega, hn', prefixOnes_append u b k hb,
      ih u hu, hdigits]

-- Past position zero, all additional digits in the prefix are zero.
private theorem prefixOnes_stable (n k i : ℕ) (hi : k + 1 ≤ i) :
    prefixOnes n k i = prefixOnes n k (k + 1) := by
  unfold prefixOnes
  symm
  refine sum_subset (range_mono hi) ?_
  intro j _ hj
  have hjk : k + 1 ≤ j := Nat.le_of_not_gt fun h => hj (mem_range.mpr h)
  exact takagiBit_neg _ _ (by omega)

private theorem takagiNewdef_split (n k : ℕ) :
    takagiNewdef n k =
      (∑ i ∈ range (k + 1), (takagiEll n k (i + 1) : ℝ) / 2 ^ (i + 1)) +
        (prefixOnes n k (k + 1) : ℝ) / 2 ^ (k + 1) := by
  let f (i : ℕ) : ℝ := (takagiEll n k (i + 1) : ℝ) / 2 ^ (i + 1)
  have htail (i : ℕ) : f (i + (k + 1)) =
      (prefixOnes n k (k + 1) : ℝ) / 2 ^ (k + 1) / 2 / 2 ^ i := by
    have hneg : (k : ℤ) - (↑(i + (k + 1)) : ℤ) < 0 := by omega
    dsimp only [f]
    rw [takagiEll_succ, takagiBit_neg _ _ hneg, ite_eq_left rfl]
    change (prefixOnes n k (i + (k + 1)) : ℝ) / _ = _
    rw [prefixOnes_stable n k _ (Nat.le_add_left _ _),
      show i + (k + 1) + 1 = (k + 1 + 1) + i by omega, pow_add, pow_succ, div_div, div_div,
      mul_assoc]
  have hs : Summable f := (summable_nat_add_iff (k + 1)).mp <|
    (summable_geometric_two' _).congr fun i => (htail i).symm
  rw [takagiNewdef_eq]
  change (∑' i, f i) = _
  rw [← hs.sum_add_tsum_nat_add (k + 1)]
  simp_rw [htail, tsum_geometric_two']
  rfl

-- This also applies to the presentation of the right endpoint.
private theorem takagiNewdef_even (n k : ℕ) :
    takagiNewdef (2 * n) k = takagiNewdef n ((k : ℤ) - 1) := by
  have hbit (j : ℤ) : takagiBit (2 * n) j = takagiBit n (j - 1) := by
    rw [← Nat.add_zero (2 * n), takagiBit_append n 0 (by decide)]
    split
    · rename_i h
      exact (takagiBit_neg _ _ (by omega)).symm
    · rfl
  simp only [takagiNewdef_eq, takagiEll_succ, hbit, sub_right_comm (k : ℤ)]

private theorem takagiNewdef_odd_sub_even (n k : ℕ) :
    takagiNewdef (2 * n + 1) k - takagiNewdef (2 * n) k =
      ((k : ℝ) + 1 - 2 * (prefixOnes n ((k : ℤ) - 1) k : ℝ)) / 2 ^ (k + 1) := by
  have hell (b i : ℕ) (hb : b < 2) (hi : i < k) :
      takagiEll (2 * n + b) k (i + 1) = takagiEll n ((k : ℤ) - 1) (i + 1) := by
    rw [takagiEll_succ, takagiEll_succ, takagiBit_append n b hb,
      ite_eq_right (by omega : (k : ℤ) - i ≠ 0), sub_right_comm (k : ℤ)]
    change (if takagiBit n ((k : ℤ) - 1 - i) = 0 then prefixOnes (2 * n + b) k i
      else i - prefixOnes (2 * n + b) k i) = _
    rw [prefixOnes_append_of_le n b k i hb hi.le]
    rfl
  have hlast (b : ℕ) (hb : b < 2) :
      takagiEll (2 * n + b) k (k + 1) = if b = 0 then prefixOnes n ((k : ℤ) - 1) k
        else k - prefixOnes n ((k : ℤ) - 1) k := by
    rw [takagiEll_succ, sub_self, takagiBit_append n b hb, ite_eq_left rfl]
    change (if b = 0 then prefixOnes (2 * n + b) k k else k - prefixOnes (2 * n + b) k k) = _
    rw [prefixOnes_append_of_le n b k k hb le_rfl]
  have hsum :
      (∑ i ∈ range k, (takagiEll (2 * n + 1) k (i + 1) : ℝ) / 2 ^ (i + 1)) =
        ∑ i ∈ range k, (takagiEll (2 * n + 0) k (i + 1) : ℝ) / 2 ^ (i + 1) := by
    refine sum_congr rfl fun i hi => ?_
    rw [hell 1 i one_lt_two (mem_range.mp hi), hell 0 i two_pos (mem_range.mp hi)]
  have hw : prefixOnes n ((k : ℤ) - 1) k ≤ k := by
    unfold prefixOnes
    calc
      _ ≤ ∑ _j ∈ range k, (1 : ℕ) := by
        refine sum_le_sum fun j hj => ?_
        have hjk := mem_range.mp hj
        rw [takagiBit_of_nonneg _ (by omega), Nat.toNat_testBit]
        exact Nat.le_of_lt_succ (Nat.mod_lt _ two_pos)
      _ = k := by simp
  change takagiNewdef (2 * n + 1) k - takagiNewdef (2 * n + 0) k = _
  rw [takagiNewdef_split (2 * n + 1), takagiNewdef_split (2 * n + 0), sum_range_succ,
    sum_range_succ, hsum, hlast 1 one_lt_two, hlast 0 two_pos, ite_eq_right one_ne_zero,
    ite_eq_left rfl, prefixOnes_append n 1 k one_lt_two, prefixOnes_append n 0 k two_pos,
    add_zero, Nat.cast_sub hw, Nat.cast_add, Nat.cast_one]
  generalize (∑ i ∈ range k, (takagiEll (2 * n) k (i + 1) : ℝ) / 2 ^ (i + 1)) = s
  ring_nf

private theorem scaled_takagi_sub (k r : ℕ) (hr : r < 2 ^ k) :
    2 ^ k * (takagiNewdef r ((k : ℤ) - 1) - takagiNewdef (r + 1) ((k : ℤ) - 1)) =
      2 * ((Nat.digits 2 r).sum : ℝ) - k := by
  induction k generalizing r with
  | zero =>
    have hzero (n : ℕ) : takagiNewdef n (-1) = 0 := by
      have hbit (i : ℕ) : takagiBit n (-1 - (i : ℤ)) = 0 := takagiBit_neg _ _ (by omega)
      simp [takagiNewdef_eq, takagiEll_succ, hbit]
    have : r = 0 := by simpa using hr
    simp [this, hzero]
  | succ k ih =>
    let u := r / 2
    have hu : u < 2 ^ k := by
      rw [pow_succ] at hr
      omega
    have hw (b : ℕ) (hb : b < 2) :
        (Nat.digits 2 (2 * u + b)).sum = (Nat.digits 2 u).sum + b := by
      have hbound : 2 * u + b < 2 ^ (k + 1) := by rw [pow_succ]; omega
      rw [← prefixOnes_eq_digits (k + 1) _ hbound, show ((k + 1 : ℕ) : ℤ) - 1 = k by omega,
        prefixOnes_append u b k hb, prefixOnes_eq_digits k u hu]
    have hstep := (eq_div_iff (pow_ne_zero (k + 1) (by norm_num : (2 : ℝ) ≠ 0))).mp
      (takagiNewdef_odd_sub_even u k)
    rw [prefixOnes_eq_digits k u hu] at hstep
    rw [show ((k + 1 : ℕ) : ℤ) - 1 = k by omega, Nat.cast_succ]
    rcases Nat.mod_two_eq_zero_or_one r with h | h
    · rw [show r = 2 * u by omega, ← Nat.add_zero (2 * u), hw 0 two_pos, add_zero]
      linear_combination -hstep
    · rw [show r = 2 * u + 1 by omega, show 2 * u + 1 + 1 = 2 * (u + 1) by omega,
        takagiNewdef_even, hw 1 one_lt_two, Nat.cast_add, Nat.cast_one, pow_succ]
      rw [takagiNewdef_even, pow_succ] at hstep
      linear_combination hstep + 2 * ih u hu

/-- **Binary digit sum from consecutive Takagi values.** Let $k$ and $r$ be natural numbers
with $r < 2^k$, let $n = 2^k + r$, and let $s_1(n)$ be the sum of the binary digits of $n$.
Writing $\tau(m, k - 1)$ for the Takagi value of the dyadic presentation $m / 2^k$, one has
$s_1(n) = 2^{k-1} \bigl(\tau(r, k - 1) - \tau(r + 1, k - 1)\bigr) + (k + 2)/2$.

Source: Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer
Sequences 27 (2024), Article 24.2.7, Theorem 28 (`jis-2024-24.2.7-thm-28`). -/
public theorem hammingWeight_eq_takagi_diff (k r : ℕ) (hr : r < 2 ^ k) :
    ((Nat.digits 2 (2 ^ k + r)).sum : ℝ) =
      2 ^ k / 2 * (takagiNewdef r ((k : ℤ) - 1) - takagiNewdef (r + 1) ((k : ℤ) - 1)) +
        ((k : ℝ) + 2) / 2 := by
  rw [hammingWeight_two_pow_add k r hr, Nat.cast_add, Nat.cast_one]
  linear_combination -(1 / 2) * scaled_takagi_sub k r hr

end MetaMathlibExt
