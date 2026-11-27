/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Binomial
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating binomial formula for the k-Fibonacci numbers

We prove Farhi's finite alternating sum for each k-Fibonacci number by first expanding
the prefix sums of the sequence and then taking their first differences. The prefix sums
`S m = ∑ i < m, F i` satisfy `S (m + k + 1) = 2 * S (m + k) - S m`. Pascal's identity
gives the same recurrence for their binomial expansion. The generalized binomial sum follows by
reversing the coefficient transformation from the generalized sum to the alternating sum.

## References

- Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the k-Fibonacci Numbers*,
  Journal of Integer Sequences 27 (2024), Article 24.1.1, pp. 1–15, Corollaries 12 and 14,
  and Remark 15(2).
- F. T. Howard and Curtis Cooper, *Some Identities for r-Fibonacci Numbers*, The Fibonacci
  Quarterly 49 (2011), no. 3, pp. 231–243, Theorem 2.1 (the order-`k + 1` recurrence) and
  Theorem 2.4 (the earlier alternating formula, with the summation bound corrected by Farhi).
-/

namespace MetaMathlibExt

open Finset

namespace kFibonacci_eq_alternating_binomial_sum

-- Extend Pascal's triangle by zero to negative row indices.
private def binom (x : ℤ) (j : ℕ) : ℚ :=
  if 0 ≤ x then x.toNat.choose j else 0

private theorem binom_zero_of_lt {x : ℤ} {j : ℕ} (h : x < j) : binom x j = 0 := by
  by_cases hx : 0 ≤ x
  · simp [binom, hx, Nat.choose_eq_zero_of_lt (show x.toNat < j by omega)]
  · simp [binom, hx]

private theorem binom_pascal (x : ℤ) (j : ℕ) :
    binom (x + 1) (j + 1) = binom x j + binom x (j + 1) := by
  by_cases hx : 0 ≤ x
  · simp [binom, hx, show 0 ≤ x + 1 by omega, show (x + 1).toNat = x.toNat + 1 by omega,
      Nat.choose_succ_succ]
  · rw [binom_zero_of_lt (by omega), binom_zero_of_lt (by omega), binom_zero_of_lt (by omega),
      add_zero]

private theorem binom_eq_choose {x : ℤ} (hx : 0 ≤ x) (j : ℕ) :
    binom x j = (Ring.choose x j : ℤ) := by
  lift x to ℕ using hx
  simp [binom, Ring.choose_natCast]

-- Of the t - k * j steps in a path of total length t, choose j to have length k + 1.
-- Each long step has weight -1 and each unit step has weight 2.
private def term (k t : ℤ) (j : ℕ) : ℚ :=
  (-1) ^ j * binom (t - k * j) j * 2 ^ (t - (k + 1) * j)

private theorem term_zero_of_lt {k t : ℤ} {j : ℕ} (h : t < (k + 1) * j) :
    term k t j = 0 := by
  simp [term, binom_zero_of_lt (show t - k * j < j by linarith)]

private theorem term_zero_index (k : ℤ) {t : ℤ} (ht : 0 ≤ t) :
    term k t 0 = 2 ^ t := by simp [term, binom, ht]

private theorem term_succ (k t : ℤ) (j : ℕ) :
    term k (t + 1) (j + 1) = 2 * term k t (j + 1) - term k (t - k) j := by
  simp only [term, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [show t + 1 - k * (j + 1) = (t - k * (j + 1)) + 1 by ring,
    binom_pascal, show t - k - k * j = t - k * (j + 1) by ring,
    show t + 1 - (k + 1) * (j + 1) = (t - (k + 1) * (j + 1)) + 1 by ring,
    show t - k - (k + 1) * j = (t - (k + 1) * (j + 1)) + 1 by ring,
    zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
  ring

private def expansion (k t : ℤ) (b : ℕ) : ℚ :=
  ∑ j ∈ range (b + 1), term k t j

private theorem expansion_succ {k t : ℤ} {b : ℕ} (ht : 0 ≤ t)
    (hb : t + 1 < (k + 1) * (b + 1)) :
    expansion k (t + 1) b = 2 * expansion k t b - expansion k (t - k) b := by
  -- The last term dropped when shifting the summation index lies outside the triangle.
  have hlast : term k (t - k) b = 0 := term_zero_of_lt (by linarith)
  unfold expansion
  rw [sum_range_succ' (term k (t + 1)), sum_range_succ' (term k t),
    sum_range_succ (term k (t - k)), hlast, add_zero]
  simp only [term_succ, sum_sub_distrib, ← mul_sum, term_zero_index k ht,
    term_zero_index k (show 0 ≤ t + 1 by omega), zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
  ring

private def prefixSum (F : ℕ → ℤ) (m : ℕ) : ℚ :=
  ∑ i ∈ range m, (F i : ℚ)

private theorem prefix_step {k : ℕ} {F : ℕ → ℤ}
    (hrec : ∀ m, F (m + k) = ∑ i ∈ range k, F (m + i)) (m : ℕ) :
    prefixSum F (m + k + 1) = 2 * prefixSum F (m + k) - prefixSum F m := by
  have h : (F (m + k) : ℚ) = ∑ i ∈ range k, (F (m + i) : ℚ) := by exact_mod_cast hrec m
  simp only [prefixSum, sum_range_succ, h, sum_range_add]
  ring

private theorem prefix_eq_expansion {k : ℕ} (hk : 2 ≤ k) {F : ℕ → ℤ}
    (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ range k, F (m + i)) (t b : ℕ)
    (hb : (t : ℤ) < (k + 1) * (b + 1)) :
    prefixSum F (t + k) = expansion k t b := by
  have hinit (m : ℕ) (hm : m < k) : prefixSum F m = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [hF0 i (by have := mem_range.mp hi; omega), Int.cast_zero]
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    cases t with
    | zero =>
      have hbase : prefixSum F k = 1 := by
        have hsplit : prefixSum F (k - 1 + 1) = prefixSum F (k - 1) + F (k - 1) :=
          sum_range_succ ..
        rw [Nat.sub_add_cancel (by omega), hinit (k - 1) (by omega), hF1] at hsplit
        simpa using hsplit
      rw [Nat.zero_add, hbase, Nat.cast_zero, expansion, sum_eq_single 0,
        term_zero_index _ le_rfl, zpow_zero]
      · intro j _ hj
        exact term_zero_of_lt (mul_pos (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero hj))
      · simp
    | succ t =>
      simp only [Nat.cast_succ] at hb ⊢
      rw [Nat.succ_add, prefix_step hrec, expansion_succ (by positivity) hb,
        ih t (by omega) (by omega)]
      congr 1
      by_cases hkt : k ≤ t
      · have heq := ih (t - k) (by omega) (by
          rw [Nat.cast_sub hkt]
          have : (0 : ℤ) ≤ k := by positivity
          omega)
        rwa [Nat.sub_add_cancel hkt, Nat.cast_sub hkt] at heq
      · rw [hinit _ (by omega), expansion]
        symm
        apply sum_eq_zero
        intro j _
        apply term_zero_of_lt
        have : (0 : ℤ) ≤ ((k : ℤ) + 1) * j := by positivity
        omega

private theorem choose_difference (x : ℤ) {j : ℕ} (hj : 1 ≤ j) :
    2 * Ring.choose (x + 1) j - Ring.choose x j =
      Ring.choose (x + 2) j - (if j = 1 then 0 else Ring.choose x (j - 2)) := by
  cases j with
  | zero => omega
  | succ j =>
    cases j with
    | zero => simp; ring
    | succ j =>
      simp [show x + 2 = x + 1 + 1 by ring, Ring.choose_succ_succ]
      ring

private theorem term_difference {k t : ℤ} {j : ℕ} (hj : 1 ≤ j) (hx : 0 ≤ t - k * j) :
    term k (t + 1) j - term k t j =
      (-1) ^ j * ((Ring.choose (t - k * j + 2) j -
        (if j = 1 then 0 else Ring.choose (t - k * j) (j - 2)) : ℤ) : ℚ) *
        2 ^ (t - (k + 1) * j) := by
  rw [← choose_difference _ hj]
  simp only [term, show t + 1 - k * j = t - k * j + 1 by ring,
    binom_eq_choose hx, binom_eq_choose (show 0 ≤ t - k * j + 1 by omega),
    show t + 1 - (k + 1) * j = t - (k + 1) * j + 1 by ring,
    zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast
  ring

end kFibonacci_eq_alternating_binomial_sum

open kFibonacci_eq_alternating_binomial_sum

/-- **Alternating binomial formula for the $k$-Fibonacci numbers.** Let $k \ge 2$ be a natural
number and let $F_n^{(k)}$ be the $k$-Fibonacci numbers: $F_i^{(k)} = 0$ for $i < k - 1$,
$F_{k-1}^{(k)} = 1$ and $F_{m+k}^{(k)} = F_m^{(k)} + F_{m+1}^{(k)} + \cdots + F_{m+k-1}^{(k)}$ for
every $m \ge 0$. For an integer $x$ and a natural number $j$ let
$\binom{x}{j} = x(x-1)\cdots(x-j+1)/j!$. Then for every natural number $n \ge k$,
$$
F_n^{(k)} = 2^{n-k} + \sum_{\ell=1}^{\lfloor (n-k+1)/(k+1) \rfloor} (-1)^\ell
\left(\binom{n - (\ell+1)k + 2}{\ell} - \binom{n - (\ell+1)k}{\ell - 2}\right)
2^{n - (k+1)\ell - k},
$$
where the term $\binom{n - (\ell+1)k}{\ell - 2}$ is taken to be $0$ for $\ell = 1$.

The paper assumes $n \ne 2k - 1$; for $n = 2k - 1$ the sum is empty and both sides equal
$2^{k-1}$.

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Corollary 14 (`jis-2024-24.1.1-cor-14`). -/
public theorem kFibonacci_eq_alternating_binomial_sum (k n : ℕ) (hk : 2 ≤ k)
    (hkn : k ≤ n) (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F n : ℚ) = 2 ^ (n - k) + ∑ ℓ ∈ Finset.Icc 1 ((n - k + 1) / (k + 1)),
      (-1) ^ ℓ * ((Ring.choose ((n : ℤ) - (ℓ + 1) * k + 2) ℓ -
        (if ℓ = 1 then 0 else Ring.choose ((n : ℤ) - (ℓ + 1) * k) (ℓ - 2)) : ℤ) : ℚ) *
        (2 : ℚ) ^ ((n : ℤ) - (k + 1) * ℓ - k) := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' hkn
  rw [Nat.add_sub_cancel]
  let b := (t + 1) / (k + 1)
  have hbound : t + 1 < (b + 1) * (k + 1) :=
    (Nat.div_lt_iff_lt_mul (by omega)).mp (Nat.lt_succ_self b)
  have hb : (t : ℤ) + 1 < (k + 1) * (b + 1) := by
    rw [mul_comm]
    exact_mod_cast hbound
  have hdiff : (F (t + k) : ℚ) = prefixSum F (t + 1 + k) - prefixSum F (t + k) := by
    rw [show t + 1 + k = t + k + 1 by omega, prefixSum, sum_range_succ]
    simp [prefixSum]
  rw [hdiff, prefix_eq_expansion hk hF0 hF1 hrec (t + 1) b (by exact_mod_cast hb),
    prefix_eq_expansion hk hF0 hF1 hrec t b (by omega)]
  simp only [expansion, Nat.cast_add, Nat.cast_one, ← sum_sub_distrib]
  rw [sum_range_eq_add_Ico _ (n := b + 1) (Nat.succ_pos b), Ico_add_one_right_eq_Icc 1 b,
    term_zero_index _ (by positivity), term_zero_index _ (by positivity),
    zpow_add_one₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  congr 1
  · ring
  · apply sum_congr rfl
    intro j hj
    obtain ⟨hj, hjb⟩ := mem_Icc.mp hj
    have hle : j * (k + 1) ≤ t + 1 := Nat.mul_le_of_le_div _ _ _ hjb
    have hx : 0 ≤ (t : ℤ) - k * j := by
      have h : (j : ℤ) * (k + 1) ≤ t + 1 := by exact_mod_cast hle
      have hj' : 1 ≤ (j : ℤ) := by exact_mod_cast hj
      linarith
    rw [term_difference hj hx]
    congr 2 <;> ring_nf

private theorem choose_neg_sub_choose (x : ℤ) (j : ℕ) :
    Ring.choose ((j : ℤ) - x - 1) (j + 1) - Ring.choose ((j : ℤ) - x - 1) j =
      (-1) ^ (j + 1) * (Ring.choose (x + 2) (j + 1) -
        (if j + 1 = 1 then 0 else Ring.choose x (j + 1 - 2))) := by
  rw [show (j : ℤ) - x - 1 = -(x + 1 - j) by ring, Ring.choose_neg, Ring.choose_neg]
  simp only [Units.smul_def, Int.coe_negOnePow_natCast, zsmul_eq_mul, Int.cast_id]
  rw [show x + 1 - (j : ℤ) + (↑(j + 1) : ℤ) - 1 = x + 1 by push_cast; ring,
    show x + 1 - (j : ℤ) + j - 1 = x by ring]
  calc
    _ = (-1) ^ (j + 1) * (Ring.choose (x + 1) (j + 1) + Ring.choose x j) := by
      rw [pow_succ]
      ring
    _ = _ := by
      rw [← choose_difference x (Nat.succ_pos j), Ring.choose_succ_succ x j]
      ring

/-- **Binomial-sum formula for the $k$-Fibonacci numbers.** Let $k \ge 2$ and let
$(F_n)_{n \ge 0}$ be the $k$-Fibonacci sequence, given by $F_0 = \dots = F_{k-2} = 0$,
$F_{k-1} = 1$ and $F_{m+k} = F_m + F_{m+1} + \dots + F_{m+k-1}$ for all $m \ge 0$. For integers
$a$ and $j \ge 0$ write $\binom{a}{j} = a(a-1)\cdots(a-j+1)/j!$, and put $\binom{a}{-1} = 0$.
Then for every $n \ge k$,
$$F_n = 2^{n-k} \sum_{\ell=0}^{\lfloor (n-k+1)/(k+1) \rfloor} \left(\binom{(k+1)\ell+k-n-2}{\ell} -
\binom{(k+1)\ell+k-n-2}{\ell-1}\right) 2^{-(k+1)\ell}.$$

Source: Bakir Farhi, *Some Applications of the Lagrange Inversion Formula for the
k-Fibonacci Numbers*, Journal of Integer Sequences 27 (2024), Article 24.1.1,
Corollary 12 (`jis-2024-24.1.1-cor-12`). -/
public theorem kFibonacci_eq_binomial_sum (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (F : ℕ → ℤ) (hF0 : ∀ i < k - 1, F i = 0) (hF1 : F (k - 1) = 1)
    (hrec : ∀ m, F (m + k) = ∑ i ∈ Finset.range k, F (m + i)) :
    (F n : ℚ) = 2 ^ (n - k) * ∑ ℓ ∈ Finset.range ((n - k + 1) / (k + 1) + 1),
      ((Ring.choose (((k + 1) * ℓ + k : ℕ) - (n : ℤ) - 2) ℓ -
        (if ℓ = 0 then 0 else Ring.choose (((k + 1) * ℓ + k : ℕ) - (n : ℤ) - 2) (ℓ - 1)) :
          ℤ) : ℚ) / 2 ^ ((k + 1) * ℓ) := by
  rw [kFibonacci_eq_alternating_binomial_sum k n hk hkn F hF0 hF1 hrec, mul_sum,
    sum_range_eq_add_Ico _ (Nat.succ_pos _)]
  simp only [Nat.succ_eq_add_one, Ico_add_one_right_eq_Icc, mul_zero, zero_add,
    Ring.choose_zero_right, ite_true, sub_zero, Int.cast_one, pow_zero, div_one, mul_one]
  congr 1
  apply sum_congr rfl
  intro ℓ hℓ
  have hℓpos : 0 < ℓ := (mem_Icc.mp hℓ).1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hℓpos)
  have htop : (((k + 1) * j.succ + k : ℕ) : ℤ) - n - 2 =
      (j : ℤ) - ((n : ℤ) - ((j.succ : ℤ) + 1) * k) - 1 := by
    push_cast
    ring
  have hpow : (2 : ℚ) ^ (n - k) / 2 ^ ((k + 1) * j.succ) =
      2 ^ ((n : ℤ) - (k + 1) * j.succ - k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0)]
    congr 1
    push_cast [Nat.cast_sub hkn]
    ring
  rw [ite_eq_right (Nat.succ_ne_zero j), Nat.succ_sub_one, htop, choose_neg_sub_choose,
    ← mul_div_assoc, mul_comm ((2 : ℚ) ^ (n - k)), mul_div_assoc, hpow]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]

end MetaMathlibExt
