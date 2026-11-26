/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CarlitzTypeQPolynomials

open Finset

namespace MetaMathlibExt

-- The zeroth term of `[x]^n` is the zeroth associated value.
example {q : ℝ} (hq0 : 0 < q) (x : ℝ) : ((q ^ x - 1) / (q - 1)) ^ 0 = 1 :=
  (qBracket.isCarlitzTypeWith_pow hq0).apply_zero x

-- Property (iii) leaves the constant associated sequence of `[x]^n` unchanged, so it maps `[x]^n`
-- to itself: `q^{-x} ([x]^n + (q - 1) [x]^{n+1}) = [x]^n`, that is `1 + (q - 1) [x] = q^x`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (n : ℕ) (x : ℝ) :
    q ^ (-x) * (((q ^ x - 1) / (q - 1)) ^ n + (q - 1) * ((q ^ x - 1) / (q - 1)) ^ (n + 1)) =
      ((q ^ x - 1) / (q - 1)) ^ n := by
  have h := qBracket.isCarlitzTypeWith_pow hq0
  exact ((isCarlitzTypeWith_closure q hq0 hq1 _ _ h).2.2.1 n x).trans (h n x).symm

-- Properties (i) and (iv) give `[x]^n` the same associated sequence `(q - 1) k`, so the two
-- sequences agree: `n ([x]^{n-1} + (q - 1) [x]^n) = n q^x [x]^{n-1}`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (n : ℕ) (x : ℝ) :
    n * (((q ^ x - 1) / (q - 1)) ^ (n - 1) + (q - 1) * ((q ^ x - 1) / (q - 1)) ^ n) =
      q ^ x * n * ((q ^ x - 1) / (q - 1)) ^ (n - 1) := by
  obtain ⟨h1, -, -, h4⟩ :=
    isCarlitzTypeWith_closure q hq0 hq1 _ _ (qBracket.isCarlitzTypeWith_pow hq0)
  exact (h4 n x).trans (h1 n x).symm

-- Properties (iii) and `apply_zero` together: `q^{-x} (T_0(x) + (q - 1) T_1(x)) = a_1` for every
-- Carlitz-type sequence `T` with associated sequence `a`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}
    (hT : IsCarlitzTypeWith q T a) (x : ℝ) : q ^ (-x) * (T 0 x + (q - 1) * T 1 x) = a 1 :=
  (isCarlitzTypeWith_closure q hq0 hq1 T a hT).2.2.1.apply_zero x

-- Property (ii) undoes property (i): the associated sequence `(q - 1) k a_{k-1}` produced by (i)
-- vanishes at `k = 0`, and (ii) maps the sequence back to one with associated sequence `a`.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) {T : ℕ → ℝ → ℝ} {a : ℕ → ℝ}
    (hT : IsCarlitzTypeWith q T a) :
    IsCarlitzTypeWith q
      (fun n x => q ^ (-x) * (q ^ x * ((n + 1 : ℕ) : ℝ) * T (n + 1 - 1) x) / (n + 1)) a := by
  have h1 := (isCarlitzTypeWith_closure q hq0 hq1 T a hT).1
  have h2 := (isCarlitzTypeWith_closure q hq0 hq1 _ _ h1).2.1 (by simp)
  convert h2 using 1
  funext k
  have hq : q - 1 ≠ 0 := sub_ne_zero.mpr hq1
  rw [Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

-- The hypothesis `a_0 = 0` of property (ii) cannot be dropped: for `[x]^n`, whose associated
-- sequence `1` has `a_0 = 1`, the conclusion of (ii) fails at `n = 0` and `x = 0`.
example {q : ℝ} (hq1 : q ≠ 1) :
    ¬ IsCarlitzTypeWith q (fun n x => q ^ (-x) * ((q ^ x - 1) / (q - 1)) ^ (n + 1) / (n + 1))
      fun k => 1 / ((q - 1) * (k + 1)) := by
  intro h
  have h00 : (0 : ℝ) = q - 1 := by simpa using h 0 0
  exact hq1 (sub_eq_zero.mp h00.symm)

-- At degree zero the initial bracket contributes 0^0 = 1, even for q below one.
example (S : ℕ → ℝ → ℝ)
    (hS : IsCarlitzTypeWith (1 / 2) S fun k =>
      1 / (((1 / 2 : ℝ) - 1) * qBracket (1 / 2) ((k + 2 : ℕ) : ℝ))) :
    1 / 16 * S 0 2 - S 0 0 = 5 / 4 := by
  have h := sum_qpow_mul_qBracket_pow (1 / 2) (by norm_num) (by norm_num) 2 0 2 (by decide) S hS
  norm_num [sum_range_succ] at h ⊢
  linarith

-- For q = 2 and r = n = 2, the first three summands are 0, 4 and 144.
example (S : ℕ → ℝ → ℝ)
    (hS : IsCarlitzTypeWith 2 S fun k => 1 / ((2 - 1) * qBracket 2 ((k + 2 : ℕ) : ℝ))) :
    64 * S 2 3 - S 2 0 = 148 := by
  have h := sum_qpow_mul_qBracket_pow 2 (by norm_num) (by norm_num) 2 2 3 (by decide) S hS
  norm_num [sum_range_succ, qBracket] at h
  exact h.symm

-- At degree one the initial summand is 0^0 = 1.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) : carlitzEtaPoly q 1 1 = 1 := by
  simpa [carlitzEtaPoly_one_zero hq1] using
    (sum_qpow_mul_qBracket_pow_eq_carlitzEta q hq0 hq1 1 1 Nat.one_pos).symm

-- At q = 1/2 the brackets at 0, 1 and 2 are 0, 1 and 3/2.
example : carlitzEtaPoly (1 / 2) 3 3 - carlitzEtaPoly (1 / 2) 3 0 = 51 / 16 := by
  have h := sum_qpow_mul_qBracket_pow_eq_carlitzEta (1 / 2) (by norm_num) (by norm_num)
    3 3 (by decide)
  norm_num [sum_range_succ, qBracket] at h
  linarith

-- At degree zero the first sum drops out and the second is geometric.
example {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) (N : ℕ) :
    (q - 1) * ∑ k ∈ range N, q ^ k = q ^ N - 1 := by
  simpa [carlitzBetaPoly_zero hq1] using
    sum_qpow_mul_qBracket_pow_eq_carlitzBeta q hq0 hq1 0 N

-- At degree one the k = 0 summand contributes 1. With q = 2 the k = 1 terms add 4 + 2.
example : 4 * carlitzBetaPoly 2 1 2 - carlitzBetaPoly 2 1 0 = 7 := by
  have h := sum_qpow_mul_qBracket_pow_eq_carlitzBeta 2 (by norm_num) (by norm_num) 1 2
  norm_num [sum_range_succ, qBracket] at h
  exact h.symm

-- At order two and degree zero the second sum is geometric, with negative weight at q = 1/2.
example : 1 / 16 * extendedCarlitzBetaPoly (1 / 2) 2 0 2 -
    extendedCarlitzBetaPoly (1 / 2) 2 0 0 = -(5 / 4) := by
  have h := sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta (1 / 2) (by norm_num) (by norm_num)
    2 0 2
  norm_num [sum_range_succ] at h ⊢
  linarith

-- At order two and degree one the k = 0 term contributes 1, and k = 1 contributes 8 + 8.
example : 16 * extendedCarlitzBetaPoly 2 2 1 2 - extendedCarlitzBetaPoly 2 2 1 0 = 17 := by
  have h := sum_qpow_mul_qBracket_pow_eq_extendedCarlitzBeta 2 (by norm_num) (by norm_num) 2 1 2
  norm_num [sum_range_succ, qBracket] at h
  exact h.symm

end MetaMathlibExt
