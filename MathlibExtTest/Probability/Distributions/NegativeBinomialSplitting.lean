/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.NegativeBinomialSplitting
import Mathlib.Tactic.NormNum

/-!
# Tests for negative binomial splitting

Concrete masses (the geometric case `r = 1`, the uniform beta-binomial `BB(n; 1, 1)`), the
splitting identity at a concrete point, normalization, and the junk value of the negative
binomial formula at `p = 0`.
-/

@[expose] public section

open Finset ProbabilityTheory

namespace MathlibExtTest.Probability.Distributions.NegativeBinomialSplitting

/-- `NB(1, p)` is geometric: `P(X = 0) = p`. -/
example : negBinomialPMF 1 (1 / 2) 0 = 1 / 2 := by
  simp [negBinomialPMF]

/-- `NB(1, 1/2)`: `P(X = 2) = 1/8`. -/
example : negBinomialPMF 1 (1 / 2) 2 = 1 / 8 := by
  simp [negBinomialPMF, ascPochhammer_succ_eval, Nat.factorial]
  norm_num

/-- `BB(1; 1, 1)` is uniform on `{0, 1}`. -/
example : betaBinomialPMF 1 1 1 0 = 1 / 2 := by
  simp [betaBinomialPMF]
  norm_num

/-- `BB(2; 1, 1)` is uniform on `{0, 1, 2}`. -/
example : betaBinomialPMF 2 1 1 1 = 1 / 3 := by
  simp [betaBinomialPMF, ascPochhammer_succ_eval]
  norm_num

/-- Normalization of `BB(4; 2, 3)`. -/
example : ∑ k ∈ range 5, betaBinomialPMF 4 2 3 k = 1 :=
  sum_betaBinomialPMF 4 (by norm_num) (by norm_num)

/-- Normalization of `NB(3/2, 1/3)`. -/
example : HasSum (negBinomialPMF (3 / 2) (1 / 3)) 1 :=
  hasSum_negBinomialPMF (by norm_num) (by norm_num) (by norm_num)

/-- Two geometric counts (`r₁ = r₂ = 1`) with total `2`: the split is uniform. -/
example : negBinomialPMF 1 (1 / 3) 1 * negBinomialPMF 1 (1 / 3) (2 - 1) /
    negBinomialPMF (1 + 1) (1 / 3) 2 = 1 / 3 := by
  rw [negBinomialPMF_mul_div_eq_betaBinomialPMF (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  simp [betaBinomialPMF, ascPochhammer_succ_eval]
  norm_num

/-- Junk value: at `p = 0` (outside `(0, 1]`) the real power `0 ^ r = 0` makes every mass
vanish, so the formula is not a probability law there. -/
example (k : ℕ) : negBinomialPMF 2 0 k = 0 := by
  simp [negBinomialPMF]

end MathlibExtTest.Probability.Distributions.NegativeBinomialSplitting
