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
import Mathlib.Tactic.Linarith

/-!
# Euclidean Bézout coefficients are least absolute inverses

The pair of Bézout coefficients provided by the Euclidean algorithm for `(m, n)` is
`(s₂, s₁)`: `s₂ m + s₁ n = gcd(m, n)`, with `s₂` the least absolute inverse of `m/g`
modulo `n/g` and `s₁` the least absolute inverse of `n/g` modulo `m/g`.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a Sequence of Modular
Inverse Switching Formulas", Lemma 4.
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.ModInverseSwitchingWanted

-- The strict lower bound on x gives one unit of slack because x and n are integers.
private theorem euclid_bezout_coeffs_leastAbsInverse.switchingBounds {m n x y : ℤ}
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
private theorem euclid_bezout_coeffs_leastAbsInverse.switching_bounds
    {r : ℕ → ℕ} {s : ℕ → ℤ} {N : ℕ}
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
    exact euclid_bezout_coeffs_leastAbsInverse.switchingBounds (by omega)
      (by exact_mod_cast hp) h hlo hhi

set_option linter.unusedVariables false in
/-- **The Euclidean Bézout coefficients are least absolute inverses.** Let $m > n > 1$ be
integers, write $g = \gcd(m, n)$, and let $(r_i)$, $(s_i)$ and $N$ be Euclidean switching data
with $r_0 = m/g$ and $r_1 = n/g$. Then $s_2 m + s_1 n = g$, $s_2$ is the least absolute inverse
of $m/g$ modulo $n/g$, and $s_1$ is the least absolute inverse of $n/g$ modulo $m/g$.

Source: Spiros Konstantogiannis, "The Euclidean Algorithm as a
Sequence of Modular Inverse Switching Formulas", Lemma 4. -/
theorem euclid_bezout_coeffs_leastAbsInverse
    (m n : ℕ) (h : n < m) (hn : 1 < n)
    (r : ℕ → ℕ) (s : ℕ → ℤ) (N : ℕ) (hseq : IsEuclidSwitchSeq r s N)
    (hr0 : r 0 = m / Nat.gcd m n) (hr1 : r 1 = n / Nat.gcd m n) :
    s 2 * (m : ℤ) + s 1 * (n : ℤ) = (Nat.gcd m n : ℤ) ∧
      IsLeastAbsInverse (s 2) ((m / Nat.gcd m n : ℕ) : ℤ)
        (n / Nat.gcd m n) ∧
      IsLeastAbsInverse (s 1) ((n / Nat.gcd m n : ℕ) : ℤ)
        (m / Nat.gcd m n) := by
  obtain ⟨hN, hpos, hdesc, hlast, hdiv, hs, hbez⟩ := hseq
  have hsw1 : s 2 * (r 0 : ℤ) + s 1 * (r 1 : ℤ) = 1 := by
    have h := hbez 1 le_rfl hN
    simpa using h
  rw [hr0, hr1] at hsw1
  have hm : (m : ℤ) = (Nat.gcd m n : ℤ) * ((m / Nat.gcd m n : ℕ) : ℤ) := by
    have hnat : Nat.gcd m n * (m / Nat.gcd m n) = m :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
    have hcast : ((Nat.gcd m n * (m / Nat.gcd m n) : ℕ) : ℤ) = (m : ℤ) := by
      rw [hnat]
    simpa [Nat.cast_mul] using hcast.symm
  have hncast : (n : ℤ) = (Nat.gcd m n : ℤ) * ((n / Nat.gcd m n : ℕ) : ℤ) := by
    have hnat : Nat.gcd m n * (n / Nat.gcd m n) = n :=
      Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
    have hcast : ((Nat.gcd m n * (n / Nat.gcd m n) : ℕ) : ℤ) = (n : ℤ) := by
      rw [hnat]
    simpa [Nat.cast_mul] using hcast.symm
  have hBez : s 2 * (m : ℤ) + s 1 * (n : ℤ) = (Nat.gcd m n : ℤ) := by
    have hmul : (Nat.gcd m n : ℤ) *
        (s 2 * ((m / Nat.gcd m n : ℕ) : ℤ) + s 1 * ((n / Nat.gcd m n : ℕ) : ℤ)) =
        (Nat.gcd m n : ℤ) := by
      rw [hsw1, mul_one]
    rw [hm, hncast]
    linarith [hmul]
  have hb2 : -((n / Nat.gcd m n : ℕ) : ℤ) < 2 * s 2 ∧
      2 * s 2 ≤ ((n / Nat.gcd m n : ℕ) : ℤ) := by
    have h := euclid_bezout_coeffs_leastAbsInverse.switching_bounds
      (r := r) (s := s) (N := N) ⟨hN, hpos, hdesc, hlast, hdiv, hs, hbez⟩
      (i := 1) hN
    rw [hr1] at h
    exact h
  have hb1 : -((m / Nat.gcd m n : ℕ) : ℤ) < 2 * s 1 ∧
      2 * s 1 ≤ ((m / Nat.gcd m n : ℕ) : ℤ) := by
    have h := euclid_bezout_coeffs_leastAbsInverse.switching_bounds
      (r := r) (s := s) (N := N) ⟨hN, hpos, hdesc, hlast, hdiv, hs, hbez⟩
      (i := 0) (Nat.zero_le N)
    rw [hr0] at h
    exact h
  have hmod2 : s 2 * ((m / Nat.gcd m n : ℕ) : ℤ) ≡
      1 [ZMOD ((n / Nat.gcd m n : ℕ) : ℤ)] := by
    simp [← hsw1]
  have hmod1 : s 1 * ((n / Nat.gcd m n : ℕ) : ℤ) ≡
      1 [ZMOD ((m / Nat.gcd m n : ℕ) : ℤ)] := by
    simp [← hsw1]
  exact ⟨hBez, ⟨hmod2, hb2.1, hb2.2⟩, ⟨hmod1, hb1.1, hb1.2⟩⟩

end MathlibExt.NumberTheory.ModInverseSwitchingWanted
