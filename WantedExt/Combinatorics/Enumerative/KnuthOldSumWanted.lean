/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# Knuth's old sum, generalizations and related sums

Statements from Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and
Related Sums*, INTEGERS 26 (2026), Article A19 (preprint arXiv:2412.00040, whose
Theorems 1-26 carry the same statements under a different numbering).

The paper's generalized binomial coefficient `binom(u, v) = Γ(u+1)/(Γ(v+1)Γ(u-v+1))` is
`gammaBinom`. The paper states its one-parameter families for an arbitrary real `v`; its
proofs integrate through Lemma 1, which needs `ℜv > -1`, so every such statement here
carries `-1 < v` (the hypotheses on `u`, `v` of the two-parameter statements are the
paper's own). `binom(2k, k)` and the Catalan numbers `C_k = binom(2k, k)/(k+1)` are
`Nat.choose (2 * k) k` and Mathlib's `catalan k`. Specializations displayed with
"In particular" that are the instance `v = 0` (or `u = v = 0`) of a stated identity are
not stated separately.
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

/-- The generalized binomial coefficient `binom(u, v) = Γ(u+1)/(Γ(v+1)Γ(u-v+1))` of
complex arguments. Mathlib's `Complex.Gamma` vanishes at the non-positive integers and
`x / 0 = 0`, so the value is `0` when `v` or `u - v` is a negative integer; for natural
arguments it is `Nat.choose` (`gammaBinom_natCast`).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Section 2, equation (7). -/
public noncomputable def gammaBinom (u v : ℂ) : ℂ :=
  Complex.Gamma (u + 1) / (Complex.Gamma (v + 1) * Complex.Gamma (u - v + 1))

/-- At natural arguments `gammaBinom` is the ordinary binomial coefficient, including the
value `0` for `k > n`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Section 2 (definitions of the binomial and the
generalized binomial coefficients). -/
public theorem gammaBinom_natCast (n k : ℕ) : gammaBinom n k = n.choose k := by
  unfold gammaBinom
  rcases le_or_gt k n with h | h
  · have e : (n : ℂ) - k + 1 = ((n - k : ℕ) : ℂ) + 1 := by
      rw [Nat.cast_sub h]
    rw [e, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
      Complex.Gamma_nat_eq_factorial, Nat.cast_choose ℂ h]
  · obtain ⟨d, rfl⟩ : ∃ d, k = n + d + 1 := ⟨k - n - 1, by omega⟩
    have e : (n : ℂ) - ((n + d + 1 : ℕ) : ℂ) + 1 = -(d : ℂ) := by
      push_cast; ring
    rw [e, Complex.Gamma_neg_nat_eq_zero, mul_zero, div_zero,
      Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]

/-- `binom(u, 0) = 1` for `ℜu > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Section 2, equation (7). -/
public theorem gammaBinom_zero_right (u : ℂ) (hu : -1 < u.re) : gammaBinom u 0 = 1 := by
  have h : Complex.Gamma (u + 1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  simp [gammaBinom, Complex.Gamma_one, h]

/-! ## Lemma 1: the integrals -/

/-- `∫₀^π cos^u(x/2) dx = 2^{-u} π binom(u, u/2)` for `ℜu > -1` (equation (8), first
equality).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Lemma 1 (`integers-2026-A19-lem-1`). -/
public theorem_wanted integral_cos_half_cpow (u : ℂ) (hu : -1 < u.re) :
    ∫ x in (0 : ℝ)..Real.pi, ((Real.cos (x / 2) : ℂ)) ^ u =
      (2 : ℂ) ^ (-u) * Real.pi * gammaBinom u (u / 2)

/-- `∫₀^π sin^u(x/2) dx = 2^{-u} π binom(u, u/2)` for `ℜu > -1` (equation (8), second
equality).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Lemma 1 (`integers-2026-A19-lem-1`). -/
public theorem_wanted integral_sin_half_cpow (u : ℂ) (hu : -1 < u.re) :
    ∫ x in (0 : ℝ)..Real.pi, ((Real.sin (x / 2) : ℂ)) ^ u =
      (2 : ℂ) ^ (-u) * Real.pi * gammaBinom u (u / 2)

/-- `∫₀^π cos^m x dx` is `2^{-m} π binom(m, m/2)` for even `m` and `0` for odd `m`
(equation (9)).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Lemma 1 (`integers-2026-A19-lem-1`). -/
public theorem_wanted integral_cos_pow_zero_pi (m : ℕ) :
    ∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ m =
      if Even m then Real.pi * (m.choose (m / 2) : ℝ) / 2 ^ m else 0

/-- `I(u, v) = ∫₀^π cos^u(x/2) sin^v(x/2) dx = 2^{-u-v} π binom(u, u/2) binom(v, v/2)
binom((u+v)/2, u/2)^{-1}` for `ℜu, ℜv > -1` (equation (10)).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Lemma 1 (`integers-2026-A19-lem-1`). -/
public theorem_wanted integral_cos_half_cpow_mul_sin_half_cpow (u v : ℂ) (hu : -1 < u.re)
    (hv : -1 < v.re) :
    ∫ x in (0 : ℝ)..Real.pi, ((Real.cos (x / 2) : ℂ)) ^ u * ((Real.sin (x / 2) : ℂ)) ^ v =
      (2 : ℂ) ^ (-u - v) * Real.pi * gammaBinom u (u / 2) * gammaBinom v (v / 2) *
        (gammaBinom ((u + v) / 2) (u / 2))⁻¹

/-- `J(m, v) = ∫₀^π cos^m x sin^v x dx` is `2^{-m-v} π binom(m, m/2) binom(v, v/2)
binom((m+v)/2, m/2)^{-1}` for even `m` and `0` for odd `m`, for `ℜv > -1`
(equation (11)).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Lemma 1 (`integers-2026-A19-lem-1`). -/
public theorem_wanted integral_cos_pow_mul_sin_cpow (m : ℕ) (v : ℂ) (hv : -1 < v.re) :
    ∫ x in (0 : ℝ)..Real.pi, ((Real.cos x : ℂ)) ^ m * ((Real.sin x : ℂ)) ^ v =
      if Even m then
        (2 : ℂ) ^ (-(m : ℂ) - v) * Real.pi * gammaBinom m ((m : ℂ) / 2) *
          gammaBinom v (v / 2) * (gammaBinom ((m + v) / 2) ((m : ℂ) / 2))⁻¹
      else 0

/-! ## Knuth's old sum and its generalizations -/

/-- Knuth's old sum (the Reed Dawson identity):
`∑_{k=0}^n (-1)^k binom(n,k) 2^{-k} binom(2k,k)` is `2^{-n} binom(n, n/2)` for even `n`
and `0` for odd `n`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 1 (`integers-2026-A19-thm-1`). -/
public theorem_wanted knuth_old_sum (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * ((2 * k).choose k : ℚ) / 2 ^ k =
      if Even n then (n.choose (n / 2) : ℚ) / 2 ^ n else 0

/-- The two-parameter generalization (14) of Knuth's old sum, for natural `m`, `n` and
real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 2 (`integers-2026-A19-thm-2`). -/
public theorem_wanted knuth_old_sum_gammaBinom_shift (m n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * (n.choose k : ℂ) / 2 ^ (k + m) *
          gammaBinom (2 * k + 2 * m + v) ((2 * k + 2 * m + v) / 2) *
          (gammaBinom (k + m + v) (v / 2))⁻¹ =
      if Even n then
        ∑ k ∈ range (m / 2 + 1),
          (m.choose (2 * k) : ℂ) / 2 ^ (n + 2 * k) *
            gammaBinom (2 * k + n) ((2 * k + n) / 2) *
            (gammaBinom ((2 * k + n + v) / 2) ((2 * k + n) / 2))⁻¹
      else
        -∑ k ∈ Icc 1 ((m + 1) / 2),
          (m.choose (2 * k - 1) : ℂ) / 2 ^ (n + 2 * k - 1) *
            gammaBinom (2 * k + n - 1) ((2 * k + n - 1) / 2) *
            (gammaBinom ((2 * k + n - 1 + v) / 2) ((2 * k + n - 1) / 2))⁻¹

/-- The one-parameter generalization (15) of Knuth's old sum, for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 1 (`integers-2026-A19-cor-1`). -/
public theorem_wanted knuth_old_sum_gammaBinom (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * (n.choose k : ℂ) / 2 ^ k *
          gammaBinom (2 * k + v) ((2 * k + v) / 2) * (gammaBinom (k + v) (v / 2))⁻¹ =
      if Even n then
        (n.choose (n / 2) : ℂ) / 2 ^ n * (gammaBinom ((n + v) / 2) (v / 2))⁻¹
      else 0

/-- Equation (16), the `n = 0` case of (14):
`∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k) binom((2k+v)/2, k)^{-1}
= 2^{-n} binom(2n+v, (2n+v)/2) binom(n+v, v/2)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 2 (`integers-2026-A19-cor-2`). -/
public theorem_wanted sum_choose_two_mul_inv_gammaBinom (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) k)⁻¹ =
      1 / 2 ^ n * gammaBinom (2 * n + v) ((2 * n + v) / 2) * (gammaBinom (n + v) (v / 2))⁻¹

/-- Equation (17), the `n = 1` case of (14):
`∑_{k=1}^{⌈n/2⌉} binom(n,2k-1) 2^{n-2k} binom(2k,k) binom((2k+v)/2, k)^{-1}` equals
`½ binom(2n+v+2, (2n+v+2)/2) binom(n+v+1, v/2)^{-1}
- binom(2n+v, (2n+v)/2) binom(n+v, v/2)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 2 (`integers-2026-A19-cor-2`). -/
public theorem_wanted sum_choose_two_mul_sub_one_inv_gammaBinom (n : ℕ) (v : ℝ)
    (hv : -1 < v) :
    ∑ k ∈ Icc 1 ((n + 1) / 2),
        (n.choose (2 * k - 1) : ℂ) * 2 ^ n / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) k)⁻¹ =
      1 / 2 * gammaBinom (2 * n + v + 2) ((2 * n + v + 2) / 2) *
          (gammaBinom (n + v + 1) (v / 2))⁻¹ -
        gammaBinom (2 * n + v) ((2 * n + v) / 2) * (gammaBinom (n + v) (v / 2))⁻¹

/-- Equation (18): `∑_{k=1}^{⌈n/2⌉} binom(n,2k-1)/(2k+1) = 2^{n+1}/(n+2) - 2^n/(n+1)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 1 (`integers-2026-A19-prop-1`). -/
public theorem_wanted sum_choose_odd_div_two_mul_add_one (n : ℕ) :
    ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) / (2 * k + 1) =
      2 ^ (n + 1) / (n + 2) - 2 ^ n / (n + 1)

/-- Equation (19): `∑_{k=1}^{⌈n/2⌉} binom(n,2k-1) 2^{n-2k} C_k = ½ C_{n+2} - C_{n+1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 1 (`integers-2026-A19-prop-1`). -/
public theorem_wanted sum_choose_odd_two_pow_mul_catalan (n : ℕ) :
    ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) * 2 ^ n / 2 ^ (2 * k) * catalan k =
      catalan (n + 2) / 2 - catalan (n + 1)

/-- `∑_{k=0}^n (-1)^k binom(n,k) 2^{k+m}/(k+m+1)` is
`∑_{k ≤ m/2} binom(m,2k)/(2k+n+1)` for even `n` and
`-∑_{k=1}^{⌈m/2⌉} binom(m,2k-1)/(2k+n)` for odd `n`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 2 (`integers-2026-A19-prop-2`). -/
public theorem_wanted sum_neg_one_pow_choose_two_pow_div_add_one (m n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * 2 ^ (k + m) / (k + m + 1) =
      if Even n then ∑ k ∈ range (m / 2 + 1), (m.choose (2 * k) : ℚ) / (2 * k + n + 1)
      else -∑ k ∈ Icc 1 ((m + 1) / 2), (m.choose (2 * k - 1) : ℚ) / (2 * k + n)

/-! ## Complements of Knuth's old sum -/

/-- Equation (24): `∑_{k=0}^n (-1)^k binom(2k,k) binom(2(n-k), n-k)` is
`2^n binom(n, n/2)` for even `n` and `0` for odd `n`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 3 (`integers-2026-A19-thm-3`). -/
public theorem_wanted sum_neg_one_pow_centralBinom_mul_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * ((2 * k).choose k : ℤ) * ((2 * (n - k)).choose (n - k)) =
      if Even n then 2 ^ n * (n.choose (n / 2) : ℤ) else 0

/-- `∑_{k=0}^n (-1)^k binom(n,k) binom(2k+v, (2k+v)/2) binom(2n-2k+v, (2n-2k+v)/2)
binom(n+v, (2k+v)/2)^{-1}` is `2^n binom(n, n/2) binom(v, v/2) binom((n+v)/2, v/2)^{-1}`
for even `n` and `0` for odd `n`, for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 5 (`integers-2026-A19-thm-5`). -/
public theorem_wanted sum_neg_one_pow_choose_gammaBinom_complement (n : ℕ) (v : ℝ)
    (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1 : ℂ) ^ k * (n.choose k : ℂ) * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          gammaBinom (2 * n - 2 * k + v) ((2 * n - 2 * k + v) / 2) *
          (gammaBinom (n + v) ((2 * k + v) / 2))⁻¹ =
      if Even n then
        2 ^ n * (n.choose (n / 2) : ℂ) * gammaBinom v (v / 2) *
          (gammaBinom ((n + v) / 2) (v / 2))⁻¹
      else 0

/-- `∑_{k=0}^n binom(n,k) binom(2k+v, (2k+v)/2) binom(2n-2k+v, (2n-2k+v)/2)
binom(n+v, (2k+v)/2)^{-1} = 2^{2n} binom(v, v/2)` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 6 (`integers-2026-A19-thm-6`). -/
public theorem_wanted sum_choose_gammaBinom_convolution (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          gammaBinom (2 * n - 2 * k + v) ((2 * n - 2 * k + v) / 2) *
          (gammaBinom (n + v) ((2 * k + v) / 2))⁻¹ =
      2 ^ (2 * n) * gammaBinom v (v / 2)

/-! ## Identities attached to a polynomial identity
`∑_{k=s}^n f(k) (1+t)^{p(k)} = ∑_{k=m}^r g(k) t^{q(k)}` (equation (28)) -/

/-- Equation (29): from the polynomial identity (28), for `ℜu, ℜv > -1`,
`∑ f(k) binom(p(k)+u+v+1, u+1)^{-1}
= (u+1)/(v+1) ∑ (-1)^{q(k)} g(k) binom(q(k)+u+v+1, v+1)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 7 (`integers-2026-A19-thm-7`). -/
public theorem_wanted sum_inv_gammaBinom_of_binomial_poly_identity (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (u v : ℂ) (hu : -1 < u.re) (hv : -1 < v.re) :
    ∑ k ∈ Icc s n, f k * (gammaBinom (p k + u + v + 1) (u + 1))⁻¹ =
      (u + 1) / (v + 1) *
        ∑ k ∈ Icc m r, (-1) ^ q k * g k * (gammaBinom (q k + u + v + 1) (v + 1))⁻¹

/-- Equation (31): from the polynomial identity (28), under the paper's hypotheses
`ℜv > -1`, `ℜ(2(u-p(j))+v) > -1` for `s ≤ j ≤ n` and `ℜ(2(u-q(j))+v) > -1` for `m ≤ j ≤ r`,
`∑ f(k) 2^{2p(k)} binom(2(u-p(k))+v, (2(u-p(k))+v)/2) binom(u-p(k)+v, v/2)^{-1}
= binom(v, v/2)^{-1} ∑ g(k) A(u, v, q(k))`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 8 (`integers-2026-A19-thm-8`). -/
public theorem_wanted sum_gammaBinom_shift_of_binomial_poly_identity (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (u v : ℂ) (hv : -1 < v.re) (hp : ∀ j ∈ Icc s n, -1 < (2 * (u - p j) + v).re)
    (hq : ∀ j ∈ Icc m r, -1 < (2 * (u - q j) + v).re) :
    ∑ k ∈ Icc s n,
        f k * 2 ^ (2 * p k) * gammaBinom (2 * (u - p k) + v) ((2 * (u - p k) + v) / 2) *
          (gammaBinom (u - p k + v) (v / 2))⁻¹ =
      (gammaBinom v (v / 2))⁻¹ *
        ∑ k ∈ Icc m r,
          g k * gammaBinom (2 * (u - q k) + v) ((2 * (u - q k) + v) / 2) *
            gammaBinom (2 * q k + v) ((2 * q k + v) / 2) *
            (gammaBinom (u + v) ((2 * q k + v) / 2))⁻¹

/-- Equation (32): the companion of (31) with the roles of the two sides exchanged,
`∑ (-1)^{q(k)} g(k) 2^{2q(k)} binom(2(u-q(k))+v, (2(u-q(k))+v)/2) binom(u-q(k)+v, v/2)^{-1}
= binom(v, v/2)^{-1} ∑ (-1)^{p(k)} f(k) B(u, v, p(k))`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 8 (`integers-2026-A19-thm-8`). -/
public theorem_wanted sum_gammaBinom_shift_of_binomial_poly_identity' (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (u v : ℂ) (hv : -1 < v.re) (hp : ∀ j ∈ Icc s n, -1 < (2 * (u - p j) + v).re)
    (hq : ∀ j ∈ Icc m r, -1 < (2 * (u - q j) + v).re) :
    ∑ k ∈ Icc m r,
        (-1) ^ q k * g k * 2 ^ (2 * q k) *
          gammaBinom (2 * (u - q k) + v) ((2 * (u - q k) + v) / 2) *
          (gammaBinom (u - q k + v) (v / 2))⁻¹ =
      (gammaBinom v (v / 2))⁻¹ *
        ∑ k ∈ Icc s n,
          (-1) ^ p k * f k * gammaBinom (2 * (u - p k) + v) ((2 * (u - p k) + v) / 2) *
            gammaBinom (2 * p k + v) ((2 * p k + v) / 2) *
            (gammaBinom (u + v) ((2 * p k + v) / 2))⁻¹

/-- Equation (34), corrected: from the polynomial identity (28), for `ℜv > -1` and
`ℜu - p(j) > -1` for `s ≤ j ≤ n` and `ℜu - q(j) > -1` for `m ≤ j ≤ r`,
`∑ (-1)^{p(k)} f(k) binom(u+v, u-p(k))^{-1}
= (u+v+1)/(v+1) ∑ (-1)^{q(k)} g(k) binom(u-q(k)+v+1, v+1)^{-1}`. The paper prints the last
binomial as `binom(u-q(k)+1, v+1)`; that is false (for `1 = 1`, i.e. `f = g = 1`,
`p = q = 0`, at `u = v = 1` the left side is `1/2` and the printed right side `3/2`), and
the paper's own proof (integration against `(1-x)^v` with the Beta integral) gives the
reading stated here, which agrees with the printed one at `v = 0`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 9 (`integers-2026-A19-thm-9`). -/
public theorem_wanted sum_neg_one_pow_inv_gammaBinom_of_binomial_poly_identity (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (u v : ℂ) (hv : -1 < v.re) (hp : ∀ j ∈ Icc s n, -1 < u.re - p j)
    (hq : ∀ j ∈ Icc m r, -1 < u.re - q j) :
    ∑ k ∈ Icc s n, (-1) ^ p k * f k * (gammaBinom (u + v) (u - p k))⁻¹ =
      (u + v + 1) / (v + 1) *
        ∑ k ∈ Icc m r, (-1) ^ q k * g k * (gammaBinom (u - q k + v + 1) (v + 1))⁻¹

/-- Equation (35): from the polynomial identity (28), for `ℜu, ℜv > -1`,
`∑ f(k) 2^{-2p(k)} binom(v, v/2) binom(2p(k)+u, (2p(k)+u)/2)
binom((2p(k)+u+v)/2, v/2)^{-1}` equals the same expression with `(f, p, u, v)` replaced
by `((-1)^q g, q, v, u)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 10 (`integers-2026-A19-thm-10`). -/
public theorem_wanted sum_two_param_gammaBinom_of_binomial_poly_identity (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (u v : ℂ) (hu : -1 < u.re) (hv : -1 < v.re) :
    ∑ k ∈ Icc s n,
        f k / 2 ^ (2 * p k) * gammaBinom v (v / 2) *
          gammaBinom (2 * p k + u) ((2 * p k + u) / 2) *
          (gammaBinom ((2 * p k + u + v) / 2) (v / 2))⁻¹ =
      ∑ k ∈ Icc m r,
        (-1) ^ q k * g k / 2 ^ (2 * q k) * gammaBinom u (u / 2) *
          gammaBinom (2 * q k + v) ((2 * q k + v) / 2) *
          (gammaBinom ((2 * q k + u + v) / 2) (u / 2))⁻¹

/-- Equation (36): from the polynomial identity (28), if every `q(2j)` is even and every
`q(2j+1)` is odd (for indices in `[m, r]`), then for `ℜv > -1`,
`∑ f(k) 2^{-p(k)} binom(2p(k)+v, (2p(k)+v)/2) binom(p(k)+v, v/2)^{-1}
= ∑_{k=⌊(m+1)/2⌋}^{⌊r/2⌋} g(2k) 2^{-q(2k)} binom(q(2k), q(2k)/2)
binom((q(2k)+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 1 (`integers-2026-A19-thm-11`). -/
public theorem_wanted sum_gammaBinom_of_binomial_poly_identity_q_even (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (hq_even : ∀ j, 2 * j ∈ Icc m r → Even (q (2 * j)))
    (hq_odd : ∀ j, 2 * j + 1 ∈ Icc m r → Odd (q (2 * j + 1)))
    (v : ℂ) (hv : -1 < v.re) :
    ∑ k ∈ Icc s n,
        f k / 2 ^ p k * gammaBinom (2 * p k + v) ((2 * p k + v) / 2) *
          (gammaBinom (p k + v) (v / 2))⁻¹ =
      ∑ k ∈ Icc ((m + 1) / 2) (r / 2),
        g (2 * k) / 2 ^ q (2 * k) * gammaBinom (q (2 * k)) ((q (2 * k) : ℂ) / 2) *
          (gammaBinom ((q (2 * k) + v) / 2) (v / 2))⁻¹

/-- Equation (37): from the polynomial identity (28), if every `q(2j)` is odd and every
`q(2j+1)` is even (for indices in `[m, r]`), then for `ℜv > -1` the left side of (36) equals
`∑_{k=⌊(m+2)/2⌋}^{⌈r/2⌉} g(2k-1) 2^{-q(2k-1)} binom(q(2k-1), q(2k-1)/2)
binom((q(2k-1)+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 1 (`integers-2026-A19-thm-11`). -/
public theorem_wanted sum_gammaBinom_of_binomial_poly_identity_q_odd (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (hq_odd : ∀ j, 2 * j ∈ Icc m r → Odd (q (2 * j)))
    (hq_even : ∀ j, 2 * j + 1 ∈ Icc m r → Even (q (2 * j + 1)))
    (v : ℂ) (hv : -1 < v.re) :
    ∑ k ∈ Icc s n,
        f k / 2 ^ p k * gammaBinom (2 * p k + v) ((2 * p k + v) / 2) *
          (gammaBinom (p k + v) (v / 2))⁻¹ =
      ∑ k ∈ Icc ((m + 2) / 2) ((r + 1) / 2),
        g (2 * k - 1) / 2 ^ q (2 * k - 1) *
          gammaBinom (q (2 * k - 1)) ((q (2 * k - 1) : ℂ) / 2) *
          (gammaBinom ((q (2 * k - 1) + v) / 2) (v / 2))⁻¹

/-- Equation (38): from the polynomial identity (28), if every `p(2j)` is even and every
`p(2j+1)` is odd (for indices in `[s, n]`), then for `ℜv > -1`,
`∑ g(k) (-1)^{q(k)} 2^{-q(k)} binom(2q(k)+v, (2q(k)+v)/2) binom(q(k)+v, v/2)^{-1}
= ∑_{k=⌊(s+1)/2⌋}^{⌊n/2⌋} (-1)^{p(2k)} f(2k) 2^{-p(2k)} binom(p(2k), p(2k)/2)
binom((p(2k)+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 2 (`integers-2026-A19-thm-11`). -/
public theorem_wanted sum_gammaBinom_of_binomial_poly_identity_p_even (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (hp_even : ∀ j, 2 * j ∈ Icc s n → Even (p (2 * j)))
    (hp_odd : ∀ j, 2 * j + 1 ∈ Icc s n → Odd (p (2 * j + 1)))
    (v : ℂ) (hv : -1 < v.re) :
    ∑ k ∈ Icc m r,
        g k * (-1) ^ q k / 2 ^ q k * gammaBinom (2 * q k + v) ((2 * q k + v) / 2) *
          (gammaBinom (q k + v) (v / 2))⁻¹ =
      ∑ k ∈ Icc ((s + 1) / 2) (n / 2),
        (-1) ^ p (2 * k) * f (2 * k) / 2 ^ p (2 * k) *
          gammaBinom (p (2 * k)) ((p (2 * k) : ℂ) / 2) *
          (gammaBinom ((p (2 * k) + v) / 2) (v / 2))⁻¹

/-- Equation (39): from the polynomial identity (28), if every `p(2j)` is odd and every
`p(2j+1)` is even (for indices in `[s, n]`), then for `ℜv > -1` the left side of (38) equals
`∑_{k=⌊(s+2)/2⌋}^{⌈n/2⌉} (-1)^{p(2k-1)} f(2k-1) 2^{-p(2k-1)} binom(p(2k-1), p(2k-1)/2)
binom((p(2k-1)+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 11, part 2 (`integers-2026-A19-thm-11`). -/
public theorem_wanted sum_gammaBinom_of_binomial_poly_identity_p_odd (s n m r : ℕ)
    (f g : ℕ → ℂ) (p q : ℕ → ℕ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ p k = ∑ k ∈ Icc m r, g k * t ^ q k)
    (hp_odd : ∀ j, 2 * j ∈ Icc s n → Odd (p (2 * j)))
    (hp_even : ∀ j, 2 * j + 1 ∈ Icc s n → Even (p (2 * j + 1)))
    (v : ℂ) (hv : -1 < v.re) :
    ∑ k ∈ Icc m r,
        g k * (-1) ^ q k / 2 ^ q k * gammaBinom (2 * q k + v) ((2 * q k + v) / 2) *
          (gammaBinom (q k + v) (v / 2))⁻¹ =
      ∑ k ∈ Icc ((s + 2) / 2) ((n + 1) / 2),
        (-1) ^ p (2 * k - 1) * f (2 * k - 1) / 2 ^ p (2 * k - 1) *
          gammaBinom (p (2 * k - 1)) ((p (2 * k - 1) : ℂ) / 2) *
          (gammaBinom ((p (2 * k - 1) + v) / 2) (v / 2))⁻¹

/-- Equation (41), first identity: for a polynomial identity
`∑_{k=s}^n f(k) (1+t)^k = ∑_{k=m}^r g(k) t^k` (equation (40)) and real `v > -1`,
`∑ f(k) 2^{-k} binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1}
= ∑_{k=⌊(m+1)/2⌋}^{⌊r/2⌋} g(2k) 2^{-2k} binom(2k,k) binom((2k+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 3 (`integers-2026-A19-cor-3`). -/
public theorem_wanted sum_gammaBinom_of_poly_identity (s n m r : ℕ) (f g : ℕ → ℂ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ k = ∑ k ∈ Icc m r, g k * t ^ k)
    (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ Icc s n,
        f k / 2 ^ k * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom (k + v) (v / 2))⁻¹ =
      ∑ k ∈ Icc ((m + 1) / 2) (r / 2),
        g (2 * k) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) (v / 2))⁻¹

/-- Equation (41), second identity: under the hypotheses of the first,
`∑ g(k) (-1)^k 2^{-k} binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1}
= ∑_{k=⌊(s+1)/2⌋}^{⌊n/2⌋} f(2k) 2^{-2k} binom(2k,k) binom((2k+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 3 (`integers-2026-A19-cor-3`). -/
public theorem_wanted sum_neg_one_pow_gammaBinom_of_poly_identity (s n m r : ℕ)
    (f g : ℕ → ℂ)
    (hP : ∀ t : ℂ, ∑ k ∈ Icc s n, f k * (1 + t) ^ k = ∑ k ∈ Icc m r, g k * t ^ k)
    (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ Icc m r,
        g k * (-1) ^ k / 2 ^ k * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom (k + v) (v / 2))⁻¹ =
      ∑ k ∈ Icc ((s + 1) / 2) (n / 2),
        f (2 * k) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) (v / 2))⁻¹

/-! ## Polynomial identities -/

/-- Equation (42): for `ℜu, ℜv > -1` and complex `x`,
`∑ (-1)^{n-k} binom(n,k) binom(k+u+v+1, u+1)^{-1} (1-x)^{n-k}
= (u+1)/(v+1) ∑ (-1)^k binom(n,k) binom(k+u+v+1, v+1)^{-1} x^{n-k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 12 (`integers-2026-A19-thm-12`). -/
public theorem_wanted sum_inv_gammaBinom_one_sub_pow (n : ℕ) (u v x : ℂ) (hu : -1 < u.re)
    (hv : -1 < v.re) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * (n.choose k : ℂ) * (gammaBinom (k + u + v + 1) (u + 1))⁻¹ *
          (1 - x) ^ (n - k) =
      (u + 1) / (v + 1) *
        ∑ k ∈ range (n + 1),
          (-1) ^ k * (n.choose k : ℂ) * (gammaBinom (k + u + v + 1) (v + 1))⁻¹ * x ^ (n - k)

/-- Equation (44): for real `v > -1` and complex `x`,
`∑ (-1)^{n-k} binom(n,k) 2^{-k} binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1} (1-x)^{n-k}
= ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k) binom((2k+v)/2, k)^{-1} x^{n-2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 13 (`integers-2026-A19-thm-13`). -/
public theorem_wanted knuth_poly_gammaBinom_one_sub_pow (n : ℕ) (v : ℝ) (hv : -1 < v)
    (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * (n.choose k : ℂ) / 2 ^ k * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom (k + v) (v / 2))⁻¹ * (1 - x) ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) k)⁻¹ * x ^ (n - 2 * k)

/-- Equation (45): `∑ (-1)^{n-k} binom(n,k) 2^k/(k+1) (1-x)^{n-k}
= ∑_{k ≤ n/2} binom(n,2k)/(2k+1) x^{n-2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 4 (`integers-2026-A19-cor-4`). -/
public theorem_wanted sum_choose_two_pow_div_succ_one_sub_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (-1) ^ (n - k) * (n.choose k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) / (2 * k + 1) * x ^ (n - 2 * k)

/-- Equation (46): `∑ (-1)^{n-k} binom(n,k)/(k+2) 2^{-k} binom(2(k+1), k+1) (1-x)^{n-k}
= ∑_{k ≤ n/2} binom(n,2k)/(k+1) 2^{-2k} binom(2k,k) x^{n-2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 4 (`integers-2026-A19-cor-4`). -/
public theorem_wanted sum_choose_centralBinom_succ_one_sub_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * (n.choose k : ℂ) / (k + 2) / 2 ^ k * ((2 * (k + 1)).choose (k + 1) : ℂ) *
          (1 - x) ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / (k + 1) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) * x ^ (n - 2 * k)

/-- Equation (47): for `ℜu, ℜv > -1` and complex `x`,
`binom(v, v/2) ∑ (-1)^{n-k} binom(n,k) 2^{-2k} binom(2k+u, (2k+u)/2)
binom((2k+u+v)/2, v/2)^{-1} (1-x)^{n-k}` equals the same expression with `u` and `v`
exchanged, `(-1)^{n-k}` replaced by `(-1)^k` and `(1-x)^{n-k}` by `x^{n-k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 14 (`integers-2026-A19-thm-14`). -/
public theorem_wanted two_param_poly_gammaBinom_one_sub_pow (n : ℕ) (u v x : ℂ)
    (hu : -1 < u.re) (hv : -1 < v.re) :
    gammaBinom v (v / 2) *
        ∑ k ∈ range (n + 1),
          (-1) ^ (n - k) * (n.choose k : ℂ) / 2 ^ (2 * k) *
            gammaBinom (2 * k + u) ((2 * k + u) / 2) *
            (gammaBinom ((2 * k + u + v) / 2) (v / 2))⁻¹ * (1 - x) ^ (n - k) =
      gammaBinom u (u / 2) *
        ∑ k ∈ range (n + 1),
          (-1) ^ k * (n.choose k : ℂ) / 2 ^ (2 * k) *
            gammaBinom (2 * k + v) ((2 * k + v) / 2) *
            (gammaBinom ((2 * k + u + v) / 2) (u / 2))⁻¹ * x ^ (n - k)

/-- Equation (48): `∑ (-1)^{n-k} binom(2k,k) 2^{-2k} binom(n,k) (1-x)^{n-k}
= ∑ (-1)^k binom(2k,k) 2^{-2k} binom(n,k) x^{n-k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 5 (`integers-2026-A19-cor-5`). -/
public theorem_wanted sum_centralBinom_choose_one_sub_pow_symm (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * ((2 * k).choose k : ℂ) / 2 ^ (2 * k) * (n.choose k : ℂ) *
          (1 - x) ^ (n - k) =
      ∑ k ∈ range (n + 1),
        (-1) ^ k * ((2 * k).choose k : ℂ) / 2 ^ (2 * k) * (n.choose k : ℂ) * x ^ (n - k)

/-- Equation (49): `∑ (-1)^{n-k} 2^{-2k} binom(n,k) C_{k+1} (1-x)^{n-k}
= ∑ (-1)^k 2^{-2k} binom(n,k) C_{k+1} x^{n-k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 5 (`integers-2026-A19-cor-5`). -/
public theorem_wanted sum_catalan_succ_choose_one_sub_pow_symm (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) / 2 ^ (2 * k) * (n.choose k : ℂ) * (catalan (k + 1) : ℂ) *
          (1 - x) ^ (n - k) =
      ∑ k ∈ range (n + 1),
        (-1) ^ k / 2 ^ (2 * k) * (n.choose k : ℂ) * (catalan (k + 1) : ℂ) * x ^ (n - k)

/-- Equation (50): for real `v > -1` and complex `x`,
`∑ binom(n,k) 2^{-k} binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1} (1-x)^k x^{n-k}
= ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k) binom((2k+v)/2, k)^{-1} (1-x)^{2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 15 (`integers-2026-A19-thm-15`). -/
public theorem_wanted knuth_poly_gammaBinom_mul_pow (n : ℕ) (v : ℝ) (hv : -1 < v) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) / 2 ^ k * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom (k + v) (v / 2))⁻¹ * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) k)⁻¹ * (1 - x) ^ (2 * k)

/-- Equation (52): `∑ binom(n,k) 2^{-k} binom(2k,k) (1-x)^k x^{n-k}
= ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k) (1-x)^{2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 6 (`integers-2026-A19-cor-6`). -/
public theorem_wanted sum_choose_centralBinom_one_sub_pow_mul_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) / 2 ^ k * ((2 * k).choose k : ℂ) * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) * (1 - x) ^ (2 * k)

/-- Equation (53): `∑ binom(n,k) 2^k/(k+1) (1-x)^k x^{n-k}
= ∑_{k ≤ n/2} binom(n,2k)/(2k+1) (1-x)^{2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 6 (`integers-2026-A19-cor-6`). -/
public theorem_wanted sum_choose_two_pow_div_succ_one_sub_pow_mul_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℂ) * 2 ^ k / (k + 1) * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℂ) / (2 * k + 1) * (1 - x) ^ (2 * k)

/-- Equation (54): `∑ binom(n,k) 2^{-k} C_{k+1} (1-x)^k x^{n-k}
= ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} C_k (1-x)^{2k}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Corollary 6 (`integers-2026-A19-cor-6`). -/
public theorem_wanted sum_choose_catalan_succ_one_sub_pow_mul_pow (n : ℕ) (x : ℂ) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) / 2 ^ k * (catalan (k + 1) : ℂ) * (1 - x) ^ k * x ^ (n - k) =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * (catalan k : ℂ) * (1 - x) ^ (2 * k)

/-! ## More combinatorial identities -/

/-- `∑_{k=0}^n (-1)^k binom(n,k) binom(k+u+v+1, u+1)^{-1}
= (u+1)/(v+1) binom(n+u+v+1, v+1)^{-1}` for `ℜu, ℜv > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 16 (`integers-2026-A19-thm-16`). -/
public theorem_wanted sum_neg_one_pow_choose_inv_gammaBinom (n : ℕ) (u v : ℂ)
    (hu : -1 < u.re) (hv : -1 < v.re) :
    ∑ k ∈ range (n + 1), (-1) ^ k * (n.choose k : ℂ) * (gammaBinom (k + u + v + 1) (u + 1))⁻¹ =
      (u + 1) / (v + 1) * (gammaBinom (n + u + v + 1) (v + 1))⁻¹

/-- `∑ (-1)^k binom(n,k) 2^{n-2k} binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1}
= ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k) binom((2k+v)/2, k)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 17 (`integers-2026-A19-thm-17`). -/
public theorem_wanted sum_neg_one_pow_choose_two_pow_gammaBinom (n : ℕ) (v : ℝ)
    (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1) ^ k * (n.choose k : ℂ) * 2 ^ n / 2 ^ (2 * k) *
          gammaBinom (2 * k + v) ((2 * k + v) / 2) * (gammaBinom (k + v) (v / 2))⁻¹ =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) k)⁻¹

/-- `∑ binom(n,k) 2^{-k} binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1}
= ∑_{k ≤ n/2} binom(n,2k) 2^{n-4k} binom(2k,k) binom((2k+v)/2, k)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 17 (`integers-2026-A19-thm-17`). -/
public theorem_wanted sum_choose_two_pow_gammaBinom (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (n.choose k : ℂ) / 2 ^ k * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom (k + v) (v / 2))⁻¹ =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) * 2 ^ n / 2 ^ (4 * k) * ((2 * k).choose k : ℂ) *
          (gammaBinom ((2 * k + v) / 2) k)⁻¹

/-- `∑ (-1)^k binom(n,k) 2^{n-2k} binom(2k,k) = ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 3 (`integers-2026-A19-prop-3`). -/
public theorem_wanted sum_neg_one_pow_choose_two_pow_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * 2 ^ n / 2 ^ (2 * k) *
        ((2 * k).choose k : ℚ) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ)

/-- `∑_{k ≤ n/2} binom(n,2k)/(2k+1) = 2^{n-1}/(2^n-1) ∑_{k=1}^{⌈n/2⌉} binom(n,2k-1)/k`
for `n ≠ 0`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 3 (`integers-2026-A19-prop-3`). -/
public theorem_wanted sum_choose_even_div_eq_sum_choose_odd_div (n : ℕ) (hn : n ≠ 0) :
    ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / (2 * k + 1) =
      2 ^ (n - 1) / (2 ^ n - 1) * ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) / k

/-- `∑ (-1)^k binom(n,k) (2k+1)/(k+2) 2^{n-2k+1} C_k = ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} C_k`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 3 (`integers-2026-A19-prop-3`). -/
public theorem_wanted sum_neg_one_pow_choose_two_pow_catalan (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ k * (n.choose k : ℚ) * (2 * k + 1) / (k + 2) *
        2 ^ (n + 1) / 2 ^ (2 * k) * catalan k =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / 2 ^ (2 * k) * catalan k

/-- `∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(2k,k) = 2^{-n} binom(2n,n)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 4 (`integers-2026-A19-prop-4`). -/
public theorem_wanted sum_choose_even_centralBinom_div_four_pow (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) =
      ((2 * n).choose n : ℚ) / 2 ^ n

/-- `∑_{k ≤ n/2} binom(n,2k)/(2k+1) = 2^n/(n+1)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 4 (`integers-2026-A19-prop-4`). -/
public theorem_wanted sum_choose_even_div_two_mul_add_one (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) / (2 * k + 1) = 2 ^ n / (n + 1)

/-- `∑_{k ≤ n/2} binom(n,2k)/(k+1) 2^{-2k} binom(2k,k) = 2^{-n+1}/(n+2) (2n+1) C_n`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 4 (`integers-2026-A19-prop-4`). -/
public theorem_wanted sum_choose_even_centralBinom_div_succ (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℚ) / (k + 1) / 2 ^ (2 * k) * ((2 * k).choose k : ℚ) =
      2 / 2 ^ n / (n + 2) * (2 * n + 1) * catalan n

/-- `∑ binom(n,k) 2^{-k} binom(2k,k) = ∑_{k ≤ n/2} binom(n,2k) 2^{n-4k} binom(2k,k)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 5 (`integers-2026-A19-prop-5`). -/
public theorem_wanted sum_choose_centralBinom_div_two_pow (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) / 2 ^ k * ((2 * k).choose k : ℚ) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * 2 ^ n / 2 ^ (4 * k) * ((2 * k).choose k : ℚ)

/-- `∑_{k ≤ n/2} binom(n,2k) (2^{n-2k+1} - 2^{2k+1})/(2k+1)
= ∑_{k=1}^{⌈n/2⌉} binom(n,2k-1) 2^{2k-1}/k`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 5 (`integers-2026-A19-prop-5`). -/
public theorem_wanted sum_choose_even_two_pow_sub_div (n : ℕ) :
    ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℚ) * (2 ^ (n + 1) / 2 ^ (2 * k) - 2 ^ (2 * k + 1)) / (2 * k + 1) =
      ∑ k ∈ Icc 1 ((n + 1) / 2), (n.choose (2 * k - 1) : ℚ) * 2 ^ (2 * k - 1) / k

/-- `∑ binom(n,k) (2k+1)/(k+2) 2^{-k+1} C_k = ∑_{k ≤ n/2} binom(n,2k) 2^{n-4k} C_k`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 5 (`integers-2026-A19-prop-5`). -/
public theorem_wanted sum_choose_two_mul_add_one_div_catalan (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℚ) * (2 * k + 1) / (k + 2) * 2 / 2 ^ k * catalan k =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * 2 ^ n / 2 ^ (4 * k) * catalan k

/-- Equation (55): `∑ (-1)^{n-k} binom(n,k) binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1}
= ∑_{k ≤ n/2} binom(n,2k) binom(2k,k) binom((2k+v)/2, k)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 18 (`integers-2026-A19-thm-18`). -/
public theorem_wanted sum_neg_one_pow_sub_choose_gammaBinom (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * (n.choose k : ℂ) * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom (k + v) (v / 2))⁻¹ =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) * ((2 * k).choose k : ℂ) * (gammaBinom ((2 * k + v) / 2) k)⁻¹

/-- `∑ (-1)^{n-k} binom(n,k) binom(2k,k) = ∑_{k ≤ n/2} binom(n,k) binom(n-k,k)` (both are
the central trinomial coefficient).

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 6 (`integers-2026-A19-prop-6`). -/
public theorem_wanted sum_neg_one_pow_sub_choose_centralBinom (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ (n - k) * (n.choose k : ℤ) * ((2 * k).choose k : ℤ) =
      ∑ k ∈ range (n / 2 + 1), (n.choose k : ℤ) * ((n - k).choose k : ℤ)

/-- `∑ (-1)^{n-k} binom(n,k) 2^{2k}/(k+1) = ∑_{k ≤ n/2} binom(n,2k) 2^{2k}/(2k+1)`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 6 (`integers-2026-A19-prop-6`). -/
public theorem_wanted sum_neg_one_pow_sub_choose_four_pow_div_succ (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * 2 ^ (2 * k) / (k + 1) =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * 2 ^ (2 * k) / (2 * k + 1)

/-- `∑ (-1)^{n-k} binom(n,k) 2(2k+1)/(k+2) C_k = ∑_{k ≤ n/2} binom(n,2k) C_k`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 6 (`integers-2026-A19-prop-6`). -/
public theorem_wanted sum_neg_one_pow_sub_choose_catalan (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * (2 * (2 * k + 1)) / (k + 2) *
        catalan k =
      ∑ k ∈ range (n / 2 + 1), (n.choose (2 * k) : ℚ) * catalan k

/-- Equation (56): `∑_{k=0}^n binom(2n,2k) binom(2(n-k), n-k) binom(2k+v, (2k+v)/2)
binom((2n+v)/2, n-k)^{-1} = ∑_{k ≤ n/2} binom(n,2k) 2^{2n-2k} binom(2k,k)
binom(2k+v, (2k+v)/2) binom((4k+v)/2, k)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 19 (`integers-2026-A19-thm-19`). -/
public theorem_wanted sum_choose_two_mul_gammaBinom_even (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        ((2 * n).choose (2 * k) : ℂ) * ((2 * (n - k)).choose (n - k) : ℂ) *
          gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom ((2 * n + v) / 2) ((n : ℂ) - k))⁻¹ =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) * 2 ^ (2 * n - 2 * k) * ((2 * k).choose k : ℂ) *
          gammaBinom (2 * k + v) ((2 * k + v) / 2) * (gammaBinom ((4 * k + v) / 2) k)⁻¹

/-- Equation (57): `∑_{k=1}^n binom(2n,2k-1) binom(2(n-k+1), n-k+1)
binom(2k-1+v, (2k-1+v)/2) binom((2n+v+1)/2, n-k+1)^{-1}
= ∑_{k=1}^{⌈n/2⌉} binom(n,2k-1) 2^{2n+1-2k} binom(2k,k) binom(2k-1+v, (2k-1+v)/2)
binom((4k+v-1)/2, k)^{-1}` for real `v > -1`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 19 (`integers-2026-A19-thm-19`). -/
public theorem_wanted sum_choose_two_mul_sub_one_gammaBinom_odd (n : ℕ) (v : ℝ)
    (hv : -1 < v) :
    ∑ k ∈ Icc 1 n,
        ((2 * n).choose (2 * k - 1) : ℂ) * ((2 * (n - k + 1)).choose (n - k + 1) : ℂ) *
          gammaBinom (2 * k - 1 + v) ((2 * k - 1 + v) / 2) *
          (gammaBinom ((2 * n + v + 1) / 2) ((n : ℂ) - k + 1))⁻¹ =
      ∑ k ∈ Icc 1 ((n + 1) / 2),
        (n.choose (2 * k - 1) : ℂ) * 2 ^ (2 * n + 1 - 2 * k) * ((2 * k).choose k : ℂ) *
          gammaBinom (2 * k - 1 + v) ((2 * k - 1 + v) / 2) *
          (gammaBinom ((4 * k + v - 1) / 2) k)⁻¹

/-- Equation (60), from Waring's formula: for `n ≥ 1` and real `v > -1`,
`∑_{k ≤ n/2} (-1)^k n/(n-k) binom(n-k,k) 2^{-4k} binom(2k+v, (2k+v)/2)
= binom(2n+v, (2n+v)/2) binom(v, v/2) 2^{1-2n} binom(n+v, v/2)^{-1}`. The paper says
"non-negative integer"; at `n = 0` the factor `n/(n-k)` is `0/0`, and the paper's
derivation uses Waring's formula, which it states for positive `n` only.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Theorem 20 (`integers-2026-A19-thm-20`). -/
public theorem_wanted waring_sum_gammaBinom (n : ℕ) (hn : 0 < n) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n / 2 + 1),
        (-1) ^ k * (n : ℂ) / ((n : ℂ) - k) * ((n - k).choose k : ℂ) / 2 ^ (4 * k) *
          gammaBinom (2 * k + v) ((2 * k + v) / 2) =
      gammaBinom (2 * n + v) ((2 * n + v) / 2) * gammaBinom v (v / 2) * 2 / 2 ^ (2 * n) *
        (gammaBinom (n + v) (v / 2))⁻¹

/-- Equation (62), from Simons' identity: for real `v > -1`,
`∑ (-1)^{n-k} binom(n,k) 2^{-k} binom(n+k,k) binom(2k+v, (2k+v)/2) binom(k+v, v/2)^{-1}
= ∑_{k ≤ n/2} binom(n,2k) 2^{-2k} binom(n+2k,2k) binom(2k,k) binom((2k+v)/2, v/2)^{-1}`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 7 (`integers-2026-A19-prop-7`). -/
public theorem_wanted simons_sum_gammaBinom (n : ℕ) (v : ℝ) (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * (n.choose k : ℂ) / 2 ^ k * ((n + k).choose k : ℂ) *
          gammaBinom (2 * k + v) ((2 * k + v) / 2) * (gammaBinom (k + v) (v / 2))⁻¹ =
      ∑ k ∈ range (n / 2 + 1),
        (n.choose (2 * k) : ℂ) / 2 ^ (2 * k) * ((n + 2 * k).choose (2 * k) : ℂ) *
          ((2 * k).choose k : ℂ) * (gammaBinom ((2 * k + v) / 2) (v / 2))⁻¹

/-- From Simons' identity and equation (35): for real `u, v > -1`,
`∑ (-1)^{n-k} binom(n,k) 2^{-2k} binom(n+k,k) binom(v, v/2) binom(2k+u, (2k+u)/2)
binom((2k+u+v)/2, v/2)^{-1}` equals the same sum with `u` and `v` exchanged and
`(-1)^{n-k}` replaced by `(-1)^k`.

Source: Kunle Adegoke, *A Short Proof of Knuth's Old Sum, Generalizations and Related
Sums*, INTEGERS 26 (2026), Article A19, Proposition 8 (`integers-2026-A19-prop-8`). -/
public theorem_wanted simons_two_param_gammaBinom (n : ℕ) (u v : ℝ) (hu : -1 < u)
    (hv : -1 < v) :
    ∑ k ∈ range (n + 1),
        (-1) ^ (n - k) * (n.choose k : ℂ) / 2 ^ (2 * k) * ((n + k).choose k : ℂ) *
          gammaBinom v (v / 2) * gammaBinom (2 * k + u) ((2 * k + u) / 2) *
          (gammaBinom ((2 * k + u + v) / 2) (v / 2))⁻¹ =
      ∑ k ∈ range (n + 1),
        (-1) ^ k * (n.choose k : ℂ) / 2 ^ (2 * k) * ((n + k).choose k : ℂ) *
          gammaBinom u (u / 2) * gammaBinom (2 * k + v) ((2 * k + v) / 2) *
          (gammaBinom ((2 * k + u + v) / 2) (u / 2))⁻¹

end

end MetaMathlibExt
