/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.BinomialMoments

/-!
# Tests for the binomial second moment and variance

Boundary cases `n = 0` (point mass at `0`) and `n = 1` (Bernoulli: variance `p (1 - p)`),
the degenerate parameters `p = 0` and `p = 1` (zero variance), and a fair coin tossed four
times (variance `1`, second moment `5`, second factorial moment `3`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped unitInterval

namespace MathlibExtTest.Probability.Distributions.BinomialMoments

/-- `n = 0`: the variance is `0`. -/
example (p : I) : Var[id; Bin(ℝ, 0, p)] = 0 := by
  rw [variance_id_map_cast_binomial]
  simp

/-- `n = 1` (Bernoulli): the variance is `p (1 - p)`. -/
example (p : I) : Var[id; Bin(ℝ, 1, p)] = p * (1 - (p : ℝ)) := by
  rw [variance_id_map_cast_binomial]
  simp

/-- `p = 0` and `p = 1`: the binomial law is degenerate and has variance `0`. -/
example (n : ℕ) : Var[id; Bin(ℝ, n, 0)] = 0 ∧ Var[id; Bin(ℝ, n, 1)] = 0 := by
  simp [variance_id_map_cast_binomial]

/-- A fair coin tossed four times: `Var X = 1` and `E[X²] = 5`. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X Bin(ℝ, 4, ⟨1 / 2, by norm_num, by norm_num⟩) P) :
    Var[X; P] = 1 ∧ P[X ^ 2] = 5 := by
  rw [variance_of_hasLaw_binomial hX, integral_sq_of_hasLaw_binomial hX]
  norm_num

/-- A fair coin tossed four times: `E[X (X - 1)] = 4 · 3 · (1/2)² = 3`. -/
example {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (hX : HasLaw X Bin(ℝ, 4, ⟨1 / 2, by norm_num, by norm_num⟩) P) :
    P[fun ω => X ω * (X ω - 1)] = 3 := by
  rw [integral_mul_sub_one_of_hasLaw_binomial hX]
  norm_num

/-- Second factorial moment for `n = 2`: `E[X (X - 1)] = 2 p²`. -/
example (p : I) : ∫ x, x * (x - 1) ∂Bin(ℝ, 2, p) = 2 * (p : ℝ) ^ 2 := by
  rw [integral_mul_sub_one_map_cast_binomial]
  norm_num

end MathlibExtTest.Probability.Distributions.BinomialMoments
