/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.GCD.Basic
public import MathlibExt.NumberTheory.ModInverseSwitching
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Rankin's minimality of the Euclidean Bézout pair

The Bézout coefficients from the Euclidean algorithm minimize the sum of squares
among all Bézout pairs, from Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas".
-/

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- The strict lower bound on x gives one unit of slack because x and n are integers.
private theorem switchingBounds {m n x y : ℤ}
    (hm : 2 ≤ m) (hn : 0 < n) (hswitch : x * m + y * n = 1)
    (hlo : -n < 2 * x) (hhi : 2 * x ≤ n) :
    -m < 2 * y ∧ 2 * y ≤ m := by
  have hm₀ : 0 ≤ m := by omega
  have hgap : 1 - n ≤ 2 * x := by omega
  constructor
  · apply lt_of_mul_lt_mul_right _ hn.le
    nlinarith only [hswitch, mul_le_mul_of_nonneg_right hhi hm₀]
  · apply le_of_mul_le_mul_right _ hn
    nlinarith only [hswitch, hm, mul_le_mul_of_nonneg_right hgap hm₀]

-- Propagate the half-open bounds backwards from the final inverse, which is one.
private theorem switching_bounds {r : ℕ → ℕ} {s : ℕ → ℤ} {N : ℕ}
    (hseq : IsEuclidSwitchSeq r s N) {i : ℕ} (hi : i ≤ N) :
    -(r i : ℤ) < 2 * s (i + 1) ∧ 2 * s (i + 1) ≤ (r i : ℤ) := by
  obtain ⟨_, hpos, hdesc, hlast, _, hs, hbez⟩ := hseq
  induction hi using Nat.decreasingInduction with
  | self =>
    have h := hdesc N le_rfl
    rw [hlast] at h
    rw [hs]
    omega
  | of_succ i hi ih =>
    obtain ⟨hlo, hhi⟩ := ih
    have h := hbez (i + 1) (by omega) hi
    rw [Nat.add_sub_cancel] at h
    have hp := hpos (i + 1) (by omega)
    have hr := hdesc i hi.le
    exact switchingBounds (by omega) (by exact_mod_cast hp) h hlo hhi

-- Within half the modulus, a number minimizes its square among its residue class.
private theorem sq_le_of_bound {a R t : ℤ} (hR : 0 < R)
    (hlo : -R ≤ 2 * a) (hhi : 2 * a ≤ R) :
    a ^ 2 ≤ (a + t * R) ^ 2 := by
  have hD : (a + t * R) ^ 2 - a ^ 2 = (t * R) * (2 * a + t * R) := by ring
  have hnonneg : 0 ≤ (t * R) * (2 * a + t * R) := by
    rcases lt_trichotomy t 0 with ht | ht | ht
    · have ht1 : t ≤ -1 := by omega
      have h1 : t * R ≤ -R := by
        have hle := mul_le_mul_of_nonneg_right ht1 hR.le
        simpa using hle
      have h2 : 2 * a + t * R ≤ 0 := by linarith
      have h3 : t * R ≤ 0 := le_of_lt (mul_neg_of_neg_of_pos ht hR)
      exact mul_nonneg_of_nonpos_of_nonpos h3 h2
    · subst ht
      simp
    · have ht1 : 1 ≤ t := by omega
      have h1 : R ≤ t * R := by
        have hle := mul_le_mul_of_nonneg_right ht1 hR.le
        simpa using hle
      have h2 : 0 ≤ 2 * a + t * R := by linarith
      have h3 : 0 ≤ t * R := le_of_lt (mul_pos ht hR)
      exact mul_nonneg h3 h2
  linarith

-- Every solution of a Bézout equation is a translate of a particular one.
private theorem bezout_param {R0 R1 a b x y : ℤ}
    (hR1 : R1 ≠ 0)
    (h0 : a * R0 + b * R1 = 1) (h1 : x * R0 + y * R1 = 1) :
    ∃ t : ℤ, x = a + t * R1 ∧ y = b - t * R0 := by
  have hsub : (x - a) * R0 + (y - b) * R1 = 0 := by linear_combination h1 - h0
  have hcop : IsCoprime R1 R0 := IsCoprime.symm ⟨a, b, h0⟩
  have hdvd : R1 ∣ (x - a) * R0 := ⟨b - y, by linear_combination hsub⟩
  obtain ⟨t, ht⟩ := hcop.dvd_of_dvd_mul_right hdvd
  refine ⟨t, ?_, ?_⟩
  · linear_combination ht
  · have e1 : (y - b) * R1 = -((x - a) * R0) := by linear_combination hsub
    have e2 : (y - b) * R1 = (-(t * R0)) * R1 := by
      rw [e1, ht]
      ring
    have hy2 : y - b = -(t * R0) := mul_right_cancel₀ hR1 e2
    linear_combination hy2

/-- **Rankin's minimality of the Euclidean Bézout pair.** Let $m > n > 1$ be integers, write
$g = \gcd(m, n)$, and let $(r_i)$, $(s_i)$ and $N$ be Euclidean switching data with
$r_0 = m/g$ and $r_1 = n/g$. Then for all integers $x$ and $y$ with $xm + yn = g$, we have
$s_2^2 + s_1^2 \le x^2 + y^2$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Corollary 2. -/
theorem euclid_bezout_coeffs_sq_add_le
    (m n : ℕ) (h : n < m) (hn : 1 < n)
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr0 : r 0 = m / Nat.gcd m n) (hr1 : r 1 = n / Nat.gcd m n)
    (x y : ℤ) (hxy : x * (m : ℤ) + y * (n : ℤ) = (Nat.gcd m n : ℤ)) :
    s 2 ^ 2 + s 1 ^ 2 ≤ x ^ 2 + y ^ 2 := by
  have hb0 : -(r 0 : ℤ) < 2 * s 1 ∧ 2 * s 1 ≤ (r 0 : ℤ) :=
    switching_bounds hseq (i := 0) (Nat.zero_le N)
  have hb1 : -(r 1 : ℤ) < 2 * s 2 ∧ 2 * s 2 ≤ (r 1 : ℤ) :=
    switching_bounds hseq (i := 1) hseq.1
  obtain ⟨hN, hpos, _hdesc, _hlast, _hdiv, _hs, hswitch⟩ := hseq
  have hbez1 : s 2 * (r 0 : ℤ) + s 1 * (r 1 : ℤ) = 1 := hswitch 1 le_rfl hN
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hgpos : 0 < Nat.gcd m n := Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_right m n) hn0
  have hgne : Nat.gcd m n ≠ 0 := ne_of_gt hgpos
  have hm_eq : m = Nat.gcd m n * (m / Nat.gcd m n) := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_left m n)).symm
  have hn_eq : n = Nat.gcd m n * (n / Nat.gcd m n) := by
    rw [mul_comm]
    exact (Nat.div_mul_cancel (Nat.gcd_dvd_right m n)).symm
  have hmZ : (m : ℤ) = (Nat.gcd m n : ℤ) * ((m / Nat.gcd m n : ℕ) : ℤ) := by
    exact_mod_cast hm_eq
  have hnZ : (n : ℤ) = (Nat.gcd m n : ℤ) * ((n / Nat.gcd m n : ℕ) : ℤ) := by
    exact_mod_cast hn_eq
  have hgZ : (Nat.gcd m n : ℤ) ≠ 0 := by exact_mod_cast hgne
  rw [hmZ, hnZ] at hxy
  have hred : x * ((m / Nat.gcd m n : ℕ) : ℤ) + y * ((n / Nat.gcd m n : ℕ) : ℤ) = 1 := by
    have hfac : (Nat.gcd m n : ℤ) *
        (x * ((m / Nat.gcd m n : ℕ) : ℤ) + y * ((n / Nat.gcd m n : ℕ) : ℤ)) =
        (Nat.gcd m n : ℤ) * 1 := by linear_combination hxy
    exact mul_left_cancel₀ hgZ hfac
  rw [hr0, hr1] at hbez1
  rw [hr0] at hb0
  rw [hr1] at hb1
  have hr0pos : 0 < r 0 := hpos 0 (by omega)
  have hr1pos : 0 < r 1 := hpos 1 (by omega)
  have hM'pos : 0 < (m / Nat.gcd m n : ℕ) := by rw [← hr0]; exact hr0pos
  have hN'pos : 0 < (n / Nat.gcd m n : ℕ) := by rw [← hr1]; exact hr1pos
  have hM'Z : 0 < ((m / Nat.gcd m n : ℕ) : ℤ) := by exact_mod_cast hM'pos
  have hN'Z : 0 < ((n / Nat.gcd m n : ℕ) : ℤ) := by exact_mod_cast hN'pos
  obtain ⟨t, hxt, hyt⟩ := bezout_param (ne_of_gt hN'Z) hbez1 hred
  have hx2 : s 2 ^ 2 ≤ x ^ 2 := by
    rw [hxt]
    exact sq_le_of_bound hN'Z (le_of_lt hb1.1) hb1.2
  have hy2 : s 1 ^ 2 ≤ y ^ 2 := by
    have h := sq_le_of_bound (a := s 1) (R := ((m / Nat.gcd m n : ℕ) : ℤ))
      (t := -t) hM'Z (le_of_lt hb0.1) hb0.2
    have e : (s 1 : ℤ) - t * ((m / Nat.gcd m n : ℕ) : ℤ) =
        s 1 + -t * ((m / Nat.gcd m n : ℕ) : ℤ) := by ring
    rw [hyt, e]
    exact h
  exact add_le_add hx2 hy2

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
