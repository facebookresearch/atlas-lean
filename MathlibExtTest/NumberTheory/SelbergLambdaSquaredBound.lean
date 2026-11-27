/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergLambdaSquaredBound
import Mathlib.Tactic.NormNum

/-!
# Tests for Selberg's Λ² upper bound
-/

namespace MathlibExtTest.NumberTheory.SelbergLambdaSquaredBound

open MathlibExt.SelbergSieve

/-- With `λ = 1` at `1` and `0` elsewhere, the bound is the trivial bound `#A`. -/
example (A : Finset ℕ) (P : ℕ) (hP : P ≠ 0) :
    ((A.filter fun n => Nat.Coprime P n).card : ℝ) ≤
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        (if d = 1 then (1 : ℝ) else 0) * (if e = 1 then (1 : ℝ) else 0) *
          ((A.filter fun n => Nat.lcm d e ∣ n).card : ℝ) :=
  card_filter_coprime_le_sum_lambda_sq A P hP _ (by simp)

/-- A non-degenerate instance: sifting `{1, ..., 10}` by `P = 6` with `λ_1 = 1`,
`λ_2 = λ_3 = -1/2`, `λ_6 = 0`. -/
example :
    (((Finset.Icc 1 10).filter fun n => Nat.Coprime 6 n).card : ℝ) ≤
      ∑ d ∈ (6 : ℕ).divisors, ∑ e ∈ (6 : ℕ).divisors,
        (if d = 1 then 1 else if d = 6 then 0 else (-1 / 2 : ℝ)) *
          (if e = 1 then 1 else if e = 6 then 0 else (-1 / 2 : ℝ)) *
          (((Finset.Icc 1 10).filter fun n => Nat.lcm d e ∣ n).card : ℝ) :=
  card_filter_coprime_le_sum_lambda_sq _ 6 (by norm_num) _ (by simp)

/-- The pointwise inequality at an `n` coprime to `P`. -/
example (lam : ℕ → ℝ) (h1 : lam 1 = 1) :
    (1 : ℝ) ≤ (∑ d ∈ (6 : ℕ).divisors, if d ∣ 5 then lam d else 0) ^ 2 := by
  have h := indicator_coprime_le_sq_sum 6 (by norm_num) lam h1 5
  have hc : Nat.Coprime 6 5 := by decide
  refine le_trans (le_of_eq ?_) h
  rw [ite_eq_left_iff.mpr fun h' => absurd hc h']

/-- The optimal-weight form, for any bounding sieve. -/
example (s : BoundingSieve) :
    s.siftedSum ≤ s.totalMass / levelSum s 1 +
      s.errSum (BoundingSieve.lambdaSquared (levelWeights s 1)) :=
  siftedSum_le_totalMass_div_levelSum_add_errSum s 1 le_rfl

end MathlibExtTest.NumberTheory.SelbergLambdaSquaredBound
