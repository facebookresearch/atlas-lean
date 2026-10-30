/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.InfinitelyDivisible

/-!
# Tests for infinitely divisible measures

Signature restatements of the public theorems in
`MathlibExt.Probability.InfinitelyDivisible`, plus concrete computations:
the third convolution power of `δ₂` on `ℝ` is `δ₆`, and the second
convolution power of `Poisson(1)` is `Poisson(2)`.
Additional checks cover orders zero and one, the zero Poisson rate, the probability consequence,
and the equivalence with the previous nonzero-order iterate root condition.
-/

@[expose] public section

open MeasureTheory Measure ProbabilityTheory
open scoped NNReal

namespace MathlibExtTest.Probability.InfinitelyDivisible

/-- The convolution power of `δ₂` on `ℝ`: `δ₂^3 = δ₆`. -/
theorem convPow_dirac_two_three : convPow (dirac (2 : ℝ)) 3 = dirac 6 := by
  rw [convPow_dirac]
  congr 1
  norm_num

/-- The convolution power of `Poisson(1)`: `Poisson(1)^2 = Poisson(2)`. -/
theorem convPow_poisson_one_two : convPow (poissonMeasure (1 : ℝ≥0)) 2 = poissonMeasure 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, convPow_succ_poissonMeasure]
  congr 1
  norm_num

/-- Signature restatement: the Dirac measure on `ℝ` is infinitely divisible. -/
theorem dirac_isInfinitelyDivisible (a : ℝ) : IsInfinitelyDivisible (dirac a) :=
  isInfinitelyDivisible_dirac a

/-- Signature restatement: the Poisson measure is infinitely divisible. -/
theorem poissonMeasure_isInfinitelyDivisible (r : ℝ≥0) :
    IsInfinitelyDivisible (poissonMeasure r) :=
  isInfinitelyDivisible_poissonMeasure r

/-- Signature restatement: infinite divisibility is closed under convolution. -/
theorem isInfinitelyDivisible_conv_restatement {μ η : Measure ℝ}
    (hμ : IsInfinitelyDivisible μ) (hη : IsInfinitelyDivisible η) :
    IsInfinitelyDivisible (μ ∗ η) :=
  hμ.conv hη

/-- Signature restatement: convolution powers add exponents. -/
theorem convPow_add_restatement {ν : Measure ℝ} [SFinite ν] (m n : ℕ) :
    convPow ν (m + n) = convPow ν m ∗ convPow ν n :=
  convPow_add m n

/-- Signature restatement: the convolution power of a convolution. -/
theorem convPow_conv_restatement {ν ρ : Measure ℝ} [SFinite ν] [SFinite ρ] (n : ℕ) :
    convPow (ν ∗ ρ) n = convPow ν n ∗ convPow ρ n :=
  convPow_conv n

/-- Order zero is the empty-sum law and is excluded from the root requirement. -/
theorem convPow_dirac_two_zero : convPow (dirac (2 : ℝ)) 0 = dirac 0 :=
  convPow_zero _

/-- The first convolution power preserves the original law. -/
theorem convPow_dirac_two_one : convPow (dirac (2 : ℝ)) 1 = dirac 2 :=
  convPow_one

/-- Zero is an allowed Poisson rate, including at positive convolution orders. -/
theorem convPow_poisson_zero_two :
    convPow (poissonMeasure (0 : ℝ≥0)) 2 = poissonMeasure 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, convPow_succ_poissonMeasure]
  simp

/-- No separate probability hypothesis is needed for an infinitely divisible law. -/
theorem probability_of_isInfinitelyDivisible {μ : Measure ℝ}
    (hμ : IsInfinitelyDivisible μ) : IsProbabilityMeasure μ :=
  hμ.isProbabilityMeasure

/-- The shared predicate retains the previous nonzero-order iterate interface. -/
theorem isInfinitelyDivisible_iff_iterate (μ : Measure ℝ) :
    IsInfinitelyDivisible μ ↔
      ∀ n : ℕ, n ≠ 0 → ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        μ = Nat.iterate (Measure.conv ν) (n - 1) ν :=
  isInfinitelyDivisible_iff_exists_iterate μ

end MathlibExtTest.Probability.InfinitelyDivisible
