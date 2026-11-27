/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Sqrt
public import MathlibExt.NumberTheory.ComplementarySequences
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Non-second-pentagonal numbers

Wu's interleaving method locates the requested term using the integer square root.
-/

namespace MetaMathlibExt

private def secondPentagonal (j : ℕ) : ℕ := (3 * j ^ 2 + j) / 2

private theorem two_mul_secondPentagonal (j : ℕ) :
    2 * secondPentagonal j = 3 * j ^ 2 + j := by
  have he : Even (3 * j ^ 2 + j) := by
    rw [show 3 * j ^ 2 + j = j * (j + 1) + 2 * j ^ 2 by ring]
    exact (Nat.even_mul_succ_self j).add (even_two.mul_right _)
  exact Nat.mul_div_cancel' he.two_dvd

@[expose] public section

/-- **Formula for the non-second-pentagonal numbers.** For every integer $n \ge 1$, put
$s = \lfloor \sqrt{2n/3} \rfloor$. Then the $n$-th positive integer that is not a second
pentagonal number $(3j^2 + j)/2$ with $j \ge 1$ equals $n + s + 1$ if $s (3s + 5) + 4 \le 2n$, and
$n + s$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Theorem 6. -/
public theorem nthNonValue_secondPentagonal (n : ℕ) (hn : 1 ≤ n) :
    let s := Nat.sqrt (2 * n / 3)
    nthNonValue (fun j => (3 * j ^ 2 + j) / 2) n =
      if s * (3 * s + 5) + 4 ≤ 2 * n then n + s + 1 else n + s := by
  let s (m : ℕ) := Nat.sqrt (2 * m / 3)
  -- The interleaving index must be positive, even at n = 1 where the square root is zero.
  let h (m : ℕ) := if m = 1 then 1 else s m
  let α (j : ℕ) : ℝ := if j = 1 then 1 else 3 * (j : ℝ) ^ 2 / 2
  have hs (m : ℕ) : s m ^ 2 * 3 ≤ 2 * m ∧ 2 * m < (s m + 1) ^ 2 * 3 := by
    exact ⟨(Nat.le_div_iff_mul_le (by decide)).mp (Nat.sqrt_le' _),
      (Nat.div_lt_iff_lt_mul (by decide)).mp (by
        simpa [s, pow_two] using Nat.lt_succ_sqrt (2 * m / 3))⟩
  have hspos (m : ℕ) (hm : m ≠ 1) (hmpos : 1 ≤ m) : 1 ≤ s m := by
    apply Nat.le_sqrt'.mpr
    omega
  have hgap (j : ℕ) (_ : 1 ≤ j) : secondPentagonal j + j ≤ secondPentagonal (j + 1) := by
    have hnext : 2 * secondPentagonal (j + 1) = 2 * secondPentagonal j + (6 * j + 4) := by
      rw [two_mul_secondPentagonal, two_mul_secondPentagonal]
      ring
    omega
  have hvalue (j : ℕ) : (secondPentagonal j : ℝ) = (3 * (j : ℝ) ^ 2 + j) / 2 := by
    apply (eq_div_iff (by norm_num)).mpr
    rw [mul_comm]
    exact_mod_cast two_mul_secondPentagonal j
  have hα (j : ℕ) (hj : 2 ≤ j) :
      (secondPentagonal (j - 1) : ℝ) ≤ α j ∧ α j ≤ secondPentagonal j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simp only [α, ite_eq_right (by omega : i + 1 ≠ 1), Nat.add_sub_cancel, hvalue, Nat.cast_add,
      Nat.cast_one]
    constructor <;> nlinarith only [Nat.cast_nonneg (α := ℝ) i]
  have hh (m : ℕ) (hm : 1 ≤ m) : 1 ≤ h m ∧ α (h m) ≤ m ∧ (m : ℝ) < α (h m + 1) := by
    by_cases hm1 : m = 1
    · subst m
      norm_num [h, α]
    simp only [h, ite_eq_right hm1]
    have hpos := hspos m hm1 hm
    have hlow : (s m : ℝ) ^ 2 * 3 ≤ 2 * (m : ℝ) := by exact_mod_cast (hs m).1
    have hhigh : 2 * (m : ℝ) < ((s m : ℝ) + 1) ^ 2 * 3 := by exact_mod_cast (hs m).2
    refine ⟨hpos, ?_, ?_⟩
    · by_cases hs1 : s m = 1
      · simpa [α, hs1] using (show (1 : ℝ) ≤ m by exact_mod_cast hm)
      · simp only [α, ite_eq_right hs1]
        linarith only [hlow]
    · simp only [α, ite_eq_right (by omega : s m + 1 ≠ 1), Nat.cast_add, Nat.cast_one]
      linarith only [hhigh]
  change nthNonValue secondPentagonal n =
    if s n * (3 * s n + 5) + 4 ≤ 2 * n then n + s n + 1 else n + s n
  rw [nthNonValue_eq_interleave secondPentagonal (by decide) hgap α hα h hh n hn]
  by_cases hn1 : n = 1
  · subst n
    norm_num [h, s, secondPentagonal]
  rw [show h n = s n by simp [h, hn1]]
  have hpos := hspos n hn1 hn
  have hlast := two_mul_secondPentagonal (s n)
  have hnext : 2 * secondPentagonal (s n + 1) = 2 * s n + (s n * (3 * s n + 5) + 4) := by
    rw [two_mul_secondPentagonal]
    ring
  have hcut : secondPentagonal (s n + 1) ≤ n + s n ↔ s n * (3 * s n + 5) + 4 ≤ 2 * n := by
    omega
  have hbefore : ¬ n + s n ≤ secondPentagonal (s n) := by
    have hlo := (hs n).1
    rw [mul_comm] at hlo
    omega
  simp only [hcut, ite_eq_right hbefore]

end

end MetaMathlibExt
