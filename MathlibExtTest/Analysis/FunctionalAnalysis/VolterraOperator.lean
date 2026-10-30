/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.FunctionalAnalysis.VolterraOperator

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.VolterraOperatorTest

open MathlibExt.Analysis.FunctionalAnalysis.VolterraOperator
open scoped BoundedContinuousFunction

/-- The Volterra operator sends the constant function `1` to the identity function. -/
example (x : Set.Icc (0 : ℝ) 1) :
    (volterraOperator (BoundedContinuousFunction.const (Set.Icc (0 : ℝ) 1) (1 : ℝ))) x
      = (x : ℝ) := by
  rw [volterraOperator_apply]
  simp [volterraExtend, intervalIntegral.integral_const]

/-- The Volterra operator sends `0` to `0`. -/
example : volterraOperator 0 = 0 :=
  map_zero _

/-- Every `Vf` vanishes at `0`, including for the constant function `2`. -/
example : (volterraOperator (BoundedContinuousFunction.const (Set.Icc (0 : ℝ) 1) (2 : ℝ)))
    ⟨0, le_refl 0, zero_le_one⟩ = 0 :=
  volterraOperator_apply_zero _

/-- Operator-norm bound for the Volterra operator. -/
example : ‖volterraOperator‖ ≤ 1 :=
  norm_volterraOperator_le_one

/-- Factorial bound for the powers of the Volterra operator. -/
example (n : ℕ) : ‖volterraOperator ^ n‖ ≤ 1 / (Nat.factorial n : ℝ) :=
  norm_volterraOperator_pow_le n

/-- The spectrum of the Volterra operator is `{0}`. -/
example : spectrum ℝ volterraOperator = {0} :=
  volterraOperator_spectrum

/-- In particular, `0` is in the spectrum of the Volterra operator. -/
example : (0 : ℝ) ∈ spectrum ℝ volterraOperator := by
  rw [volterraOperator_spectrum]
  exact Set.mem_singleton _

/-- The spectral radius of the Volterra operator is `0`. -/
example : spectralRadius ℝ volterraOperator = 0 :=
  spectralRadius_volterraOperator

end MathlibExt.Analysis.FunctionalAnalysis.VolterraOperatorTest
