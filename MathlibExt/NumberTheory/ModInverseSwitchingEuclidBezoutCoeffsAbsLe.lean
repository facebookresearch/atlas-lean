/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModInverseSwitching
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Euclidean Bézout coefficients are smallest in absolute value

This module proves `euclid_bezout_coeffs_abs_le`: for Euclidean switching data with
`r 0 = m / gcd m n` and `r 1 = n / gcd m n`, every pair of integers `x` and `y` with
`x * m + y * n = gcd m n` satisfies `|s 2| ≤ |x|` and `|s 1| ≤ |y|`. It also proves
`isLeastAbsInverse_all`: for `1 ≤ i ≤ N + 1`, `s i` is the least absolute inverse of `r i` modulo
`r (i - 1)`.

Statements from Spiros Konstantogiannis, "The Euclidean Algorithm
as a Sequence of Modular Inverse Switching Formulas", *INTEGERS*
24 (2024), Article A29
(<https://math.colgate.edu/~integers/y29/y29.pdf>,
DOI 10.5281/zenodo.10821707).
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- `ZMod.natAbs_min_of_le_div_two`, for a natural modulus and integers.
private theorem abs_le_add_mul_of_two_abs_le {n : ℕ} {s t : ℤ} (h : 2 * |s| ≤ (n : ℤ)) :
    |s| ≤ |s + t * (n : ℤ)| := by
  rw [Int.abs_eq_natAbs] at h
  simp only [Int.abs_eq_natAbs]
  exact_mod_cast ZMod.natAbs_min_of_le_div_two n s (s + t * (n : ℤ)) (by simp) (by omega)

private theorem isLeastAbsInverse_next {r : ℕ → ℕ} {s : ℕ → ℤ} {N : ℕ}
    (hseq : IsEuclidSwitchSeq r s N) {i : ℕ} (hi : i ≤ N) :
    IsLeastAbsInverse (s (i + 1)) (r (i + 1) : ℤ) (r i) := by
  have hseq' := hseq
  obtain ⟨-, -, hdesc, hlast, -, hs, -⟩ := hseq
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [hs, hlast]
    have h2 : 2 ≤ r N := by
      have h := hdesc N le_rfl
      rw [hlast] at h
      omega
    refine ⟨by simp, by omega, by omega⟩
  | of_succ i hi ih =>
    have h := isLeastAbsInverse_succ_imp r s N hseq' (i + 1) (by omega) hi ih
    rwa [Nat.add_sub_cancel] at h

/-- **Every switching inverse is a least absolute inverse.** Let $(r_i)$, $(s_i)$ and $N$ be
Euclidean switching data. Then for every $i$ with $1 \le i \le N + 1$, $s_i$ is the least
absolute inverse of $r_i$ modulo $r_{i-1}$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Corollary 1. -/
theorem isLeastAbsInverse_all
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N) :
    ∀ i : ℕ, 1 ≤ i → i ≤ N + 1 →
      IsLeastAbsInverse (s i) (r i : ℤ) (r (i - 1)) := by
  intro i hi1 hi2
  have h := isLeastAbsInverse_next hseq (i := i - 1) (by omega)
  rwa [Nat.sub_add_cancel hi1] at h

set_option linter.unusedVariables false in
/-- **The Euclidean Bézout coefficients are smallest in absolute value.** Let $m > n > 1$ be
integers, write $g = \gcd(m, n)$, and let $(r_i)$, $(s_i)$ and $N$ be Euclidean switching data
with $r_0 = m/g$ and $r_1 = n/g$. Then for all integers $x$ and $y$ with $xm + yn = g$, we have
$|s_2| \le |x|$ and $|s_1| \le |y|$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 5. -/
theorem euclid_bezout_coeffs_abs_le
    (m n : ℕ) (h : n < m) (hn : 1 < n)
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr0 : r 0 = m / Nat.gcd m n) (hr1 : r 1 = n / Nat.gcd m n)
    (x y : ℤ) (hxy : x * (m : ℤ) + y * (n : ℤ) = (Nat.gcd m n : ℤ)) :
    |s 2| ≤ |x| ∧ |s 1| ≤ |y| := by
  have hseq' := hseq
  obtain ⟨hN, hpos, -, -, -, -, hbez⟩ := hseq
  have hn0 : 0 < n := by omega
  have hg0 : 0 < Nat.gcd m n := Nat.gcd_pos_iff.mpr (Or.inr hn0)
  have hg_ne : (Nat.gcd m n : ℤ) ≠ 0 := by exact_mod_cast ne_of_gt hg0
  have hm_eq : ((r 0 : ℕ) : ℤ) * (Nat.gcd m n : ℤ) = (m : ℤ) := by
    rw [hr0]
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_left m n)
  have hn_eq : ((r 1 : ℕ) : ℤ) * (Nat.gcd m n : ℤ) = (n : ℤ) := by
    rw [hr1]
    exact_mod_cast Nat.div_mul_cancel (Nat.gcd_dvd_right m n)
  have hsw : s 2 * ((r 0 : ℕ) : ℤ) + s 1 * ((r 1 : ℕ) : ℤ) = 1 := hbez 1 le_rfl hN
  have hbez_g : s 2 * (m : ℤ) + s 1 * (n : ℤ) = (Nat.gcd m n : ℤ) := by
    linear_combination (Nat.gcd m n : ℤ) * hsw + s 2 * hm_eq.symm + s 1 * hn_eq.symm
  have hdiff : (x - s 2) * (m : ℤ) + (y - s 1) * (n : ℤ) = 0 := by
    linear_combination hxy - hbez_g
  have hdiff' : (x - s 2) * ((r 0 : ℕ) : ℤ) + (y - s 1) * ((r 1 : ℕ) : ℤ) = 0 := by
    have hfac : ((x - s 2) * ((r 0 : ℕ) : ℤ) + (y - s 1) * ((r 1 : ℕ) : ℤ)) *
        (Nat.gcd m n : ℤ) = 0 * (Nat.gcd m n : ℤ) := by
      linear_combination hdiff + (x - s 2) * hm_eq + (y - s 1) * hn_eq
    exact mul_right_cancel₀ hg_ne hfac
  have hcross : (x - s 2) * ((r 0 : ℕ) : ℤ) = (s 1 - y) * ((r 1 : ℕ) : ℤ) := by
    linear_combination hdiff'
  have hcop : Nat.Coprime (r 0) (r 1) := by
    rw [hr0, hr1]
    exact Nat.coprime_div_gcd_div_gcd hg0
  have hdvd : ((r 1 : ℕ) : ℤ) ∣ x - s 2 := by
    have h1 : ((r 1 : ℕ) : ℤ) ∣ (x - s 2) * ((r 0 : ℕ) : ℤ) := by
      rw [hcross]
      exact dvd_mul_left _ _
    exact (hcop.symm.isCoprime).dvd_of_dvd_mul_right h1
  obtain ⟨t, ht⟩ := hdvd
  have hr1pos : 0 < ((r 1 : ℕ) : ℤ) := by exact_mod_cast hpos 1 (by omega)
  have hr1ne : ((r 1 : ℕ) : ℤ) ≠ 0 := ne_of_gt hr1pos
  have hx : x = s 2 + t * ((r 1 : ℕ) : ℤ) := by linear_combination ht
  have hy : y = s 1 - t * ((r 0 : ℕ) : ℤ) := by
    have h2 : (s 1 - y) * ((r 1 : ℕ) : ℤ)
        = t * ((r 0 : ℕ) : ℤ) * ((r 1 : ℕ) : ℤ) := by
      linear_combination ht * ((r 0 : ℕ) : ℤ) - hcross
    have h3 : s 1 - y = t * ((r 0 : ℕ) : ℤ) := mul_right_cancel₀ hr1ne h2
    linear_combination -h3
  have hb1 : IsLeastAbsInverse (s 1) ((r 1 : ℕ) : ℤ) (r 0) :=
    isLeastAbsInverse_next (i := 0) hseq' (Nat.zero_le N)
  have hb2 : IsLeastAbsInverse (s 2) ((r 2 : ℕ) : ℤ) (r 1) :=
    isLeastAbsInverse_next (i := 1) hseq' hN
  have habs1 : 2 * |s 1| ≤ ((r 0 : ℕ) : ℤ) := by
    have hle := abs_le.mpr ⟨le_of_lt hb1.2.1, hb1.2.2⟩
    simpa [abs_mul] using hle
  have habs2 : 2 * |s 2| ≤ ((r 1 : ℕ) : ℤ) := by
    have hle := abs_le.mpr ⟨le_of_lt hb2.2.1, hb2.2.2⟩
    simpa [abs_mul] using hle
  constructor
  · rw [hx]
    exact abs_le_add_mul_of_two_abs_le habs2
  · rw [hy]
    have heq : s 1 - t * ((r 0 : ℕ) : ℤ) = s 1 + -t * ((r 0 : ℕ) : ℤ) := by ring
    rw [heq]
    exact abs_le_add_mul_of_two_abs_le habs1

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
