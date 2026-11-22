/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic

namespace MetaMathlibExt

@[expose] public section

/-- Generalized Stirling numbers of the first kind, after Carlitz and Broder,
as recorded in Cereceda (arXiv:2401.13696v4, lines 132-142; Axioms 14 (2025), 746):
`[n,m]_x = ∑_{i=0}^{n-m} choose (i+m) m * stirlingFirst n (i+m) * x^i`
for `m ≤ n`, with `x` real. The definition below uses the displayed finite sum
for every `n, m`; when `m > n`, `n - m + 1 = 1` and the single ordinary term
vanishes, giving `0`. -/
noncomputable def generalizedStirlingFirst (n m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i)

/-- Generalized Stirling numbers of the second kind, after Carlitz and Broder,
as recorded in Cereceda (arXiv:2401.13696v4, lines 132-142; Axioms 14 (2025), 746):
`{n,m}_x = ∑_{i=0}^{n-m} choose n i * stirlingSecond (n-i) m * x^i`
for `m ≤ n`, with `x` real. The definition below uses the displayed finite sum
for every `n, m`; when `m > n`, `n - m + 1 = 1` and the single ordinary term
vanishes, giving `0`. -/
noncomputable def generalizedStirlingSecond (n m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i)

/-- Characterization of `generalizedStirlingFirst`: under `m ≤ n` it equals the
exact source sum with coefficient `choose (i+m) m`, ordinary number
`stirlingFirst n (i+m)`, and power `x^i`, including both endpoints `i = 0` and
`i = n - m`. Source: Cereceda, arXiv:2401.13696v4, lines 132-142. -/
theorem generalizedStirlingFirst_eq_sum (n m : ℕ) (x : ℝ) (_h : m ≤ n) :
    generalizedStirlingFirst n m x =
      Finset.sum (Finset.range (n - m + 1)) (fun i =>
        (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i) := rfl

/-- Characterization of `generalizedStirlingSecond`: under `m ≤ n` it equals the
exact source sum with coefficient `choose n i`, ordinary number
`stirlingSecond (n-i) m`, and power `x^i`, including both endpoints `i = 0` and
`i = n - m`. Source: Cereceda, arXiv:2401.13696v4, lines 132-142. -/
theorem generalizedStirlingSecond_eq_sum (n m : ℕ) (x : ℝ) (_h : m ≤ n) :
    generalizedStirlingSecond n m x =
      Finset.sum (Finset.range (n - m + 1)) (fun i =>
        (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i) := rfl

end

end MetaMathlibExt
