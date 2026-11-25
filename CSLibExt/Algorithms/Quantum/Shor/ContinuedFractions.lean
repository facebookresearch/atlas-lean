/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# Continued-fraction post-processing in Shor's order-finding algorithm

After the quantum Fourier transform, Shor's order-finding algorithm observes an integer `c`
with `0 ≤ c < q`, where `q` is a power of two with `n ^ 2 ≤ q < 2 n ^ 2` and `n` is the number to
be factored. With probability bounded below, there is an integer `d` with
`|c / q - d / r| ≤ 1 / (2 q)`, where `r < n` is the unknown order (Shor 1997, Section 5,
equation (5.13)). This file proves the two classical facts Shor uses to recover `d / r` from `c`:

* `eq_of_abs_sub_le_of_lt`: because `q ≥ n ^ 2`, at most one fraction with a positive
  denominator smaller than `n` lies within `1 / (2 q)` of `c / q`;
* `exists_convergent_eq_of_abs_sub_le`: that fraction is a convergent of the continued fraction
  expansion of `c / q`, so the expansion finds it. This is Legendre's theorem
  (`Real.exists_rat_eq_convergent` in Mathlib) applied to Shor's bound.

Both statements are for an arbitrary real number `ξ` in place of `c / q`.

## Source

P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a
quantum computer*, SIAM J. Comput. 26 (1997), 1484–1509 (arXiv:quant-ph/9508027), Section 5,
equations (5.12)–(5.13) and the paragraph after them.
-/

@[expose] public section

namespace Cslib.Shor

/-- **Uniqueness of the fraction recovered in Shor's algorithm.** Let `ξ` be a real number and
let `q` and `n` be natural numbers with `n ^ 2 ≤ q`. If two fractions `d / r` and `d' / r'` with
integer numerators and denominators `0 < r < n`, `0 < r' < n` both lie within `1 / (2 q)` of
`ξ`, then they are equal.

This is Shor's remark that "because `q > n²`, there is at most one fraction `d / r` with
`r < n`" satisfying `|c / q - d / r| ≤ 1 / (2 q)` (P. W. Shor, SIAM J. Comput. 26 (1997),
Section 5, after equation (5.13)); the proof only needs `q ≥ n ^ 2`. -/
theorem eq_of_abs_sub_le_of_lt (ξ : ℝ) {q n r r' : ℕ} {d d' : ℤ} (hq : n ^ 2 ≤ q)
    (hr : 0 < r) (hr' : 0 < r') (hrn : r < n) (hr'n : r' < n)
    (h : |ξ - d / r| ≤ 1 / (2 * q)) (h' : |ξ - d' / r'| ≤ 1 / (2 * q)) :
    (d : ℝ) / r = d' / r' := by
  by_contra hne
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hr'R : (0 : ℝ) < r' := by exact_mod_cast hr'
  -- The two fractions differ by at least `1 / (r r')`.
  have hnum : d * (r' : ℤ) - d' * r ≠ 0 := by
    intro h0
    apply hne
    rw [div_eq_div_iff hrR.ne' hr'R.ne']
    have : ((d * (r' : ℤ) - d' * r : ℤ) : ℝ) = 0 := by exact_mod_cast h0
    push_cast at this
    linarith
  have hone : (1 : ℝ) ≤ |((d * (r' : ℤ) - d' * r : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |d * (r' : ℤ) - d' * r| := Int.one_le_abs hnum
    exact_mod_cast this
  have hdiff : (d : ℝ) / r - d' / r' = ((d * (r' : ℤ) - d' * r : ℤ) : ℝ) / (r * r') := by
    push_cast
    field_simp
  -- `r r' < n ^ 2 ≤ q`.
  have hrr : r * r' < q := by
    have : r * r' < n * n := Nat.mul_lt_mul'' hrn hr'n
    nlinarith
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le _) hrr
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hrrR : (r : ℝ) * r' < q := by exact_mod_cast hrr
  have hrr0 : (0 : ℝ) < r * r' := mul_pos hrR hr'R
  -- Lower bound: `|d / r - d' / r'| ≥ 1 / (r r') > 1 / q`.
  have hlow : 1 / (q : ℝ) < |(d : ℝ) / r - d' / r'| := by
    rw [hdiff, abs_div, abs_of_pos hrr0]
    calc 1 / (q : ℝ) < 1 / (r * r') := one_div_lt_one_div_of_lt hrr0 hrrR
      _ ≤ |((d * (r' : ℤ) - d' * r : ℤ) : ℝ)| / (r * r') :=
        div_le_div_of_nonneg_right hone hrr0.le
  -- Upper bound from the triangle inequality: `|d / r - d' / r'| ≤ 1 / q`.
  have hup : |(d : ℝ) / r - d' / r'| ≤ 1 / q := by
    calc |(d : ℝ) / r - d' / r'| = |(ξ - d' / r') - (ξ - d / r)| := by ring_nf
      _ ≤ |ξ - d' / r'| + |ξ - d / r| := abs_sub _ _
      _ ≤ 1 / (2 * q) + 1 / (2 * q) := add_le_add h' h
      _ = 1 / q := by field_simp; ring
  linarith

/-- **Continued fractions recover the fraction in Shor's algorithm.** Let `ξ` be a real number
and let `q` and `n` be natural numbers with `n ^ 2 ≤ q`. If an integer `d` and a natural number
`r` with `0 < r < n` satisfy `|ξ - d / r| ≤ 1 / (2 q)`, then the rational number `d / r` is a
convergent of the continued fraction expansion of `ξ`.

In Shor's algorithm `ξ = c / q` is the observed output divided by `q`, so `d / r` (in lowest
terms) is found among the polynomially many convergents of `c / q` (P. W. Shor, SIAM J.
Comput. 26 (1997), Section 5, the paragraph after equation (5.13)). The proof applies
Legendre's theorem `Real.exists_rat_eq_convergent`: the reduced denominator of `d / r` is at
most `r`, and `1 / (2 q) ≤ 1 / (2 n ^ 2) < 1 / (2 r ^ 2)`. -/
theorem exists_convergent_eq_of_abs_sub_le (ξ : ℝ) {q n r : ℕ} {d : ℤ} (hq : n ^ 2 ≤ q)
    (hr : 0 < r) (hrn : r < n) (h : |ξ - d / r| ≤ 1 / (2 * q)) :
    ∃ k, ((d : ℚ) / r : ℚ) = ξ.convergent k := by
  set Q : ℚ := (d : ℚ) / r with hQ
  apply Real.exists_rat_eq_convergent
  -- The reduced denominator of `Q` divides `r`.
  have hden : Q.den ≤ r := by
    have hdvd : ((Rat.divInt d r).den : ℤ) ∣ (r : ℤ) := Rat.den_dvd d r
    have hQ' : Q = Rat.divInt d r := by rw [Rat.divInt_eq_div, hQ]; push_cast; rfl
    have : Q.den ∣ r := by rw [hQ']; exact_mod_cast hdvd
    exact Nat.le_of_dvd hr this
  have hden0 : (0 : ℝ) < Q.den := by exact_mod_cast Q.pos
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hdenR : (Q.den : ℝ) ≤ r := by exact_mod_cast hden
  have hrq : r ^ 2 < q := by
    have : r * r < n * n := Nat.mul_lt_mul'' hrn hrn
    nlinarith
  have hrqR : (r : ℝ) ^ 2 < q := by exact_mod_cast hrq
  have hcast : ((Q : ℚ) : ℝ) = (d : ℝ) / r := by
    rw [hQ]; push_cast; ring
  rw [hcast]
  calc |ξ - d / r| ≤ 1 / (2 * q) := h
    _ < 1 / (2 * (r : ℝ) ^ 2) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    _ ≤ 1 / (2 * (Q.den : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : (Q.den : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := pow_le_pow_left₀ hden0.le hdenR 2
      linarith

end Cslib.Shor
