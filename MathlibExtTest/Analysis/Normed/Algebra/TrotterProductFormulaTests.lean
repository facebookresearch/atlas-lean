/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula

@[expose] public section

namespace MathlibExtTest.Analysis.Normed.Algebra.TrotterProductFormulaTests

open Filter Topology
open MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula

/-!
# Tests for the Trotter product formula

The scalar cases pin the statement and the commuting case pins exactness for
positive `n`. The operator reading (apply the theorem to the Banach algebra
`E →L[𝕜] E`) is not tested here: for `𝕜 = ℝ` or `ℂ` the `ℚ`-algebra instance
on continuous linear maps must be supplied via
`NormedAlgebra.restrictScalars`, whose scalar action differs syntactically
from the ambient pointwise action, so an operator test would need an
instance-equality argument rather than a direct application.
-/

/-- Trotter product formula for real scalars. -/
example (a b : ℝ) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((n : ℚ)⁻¹ • a) * NormedSpace.exp ((n : ℚ)⁻¹ • b)) ^ n)
      atTop (nhds (NormedSpace.exp (a + b))) :=
  tendsto_trotter_product a b

/-- Trotter product formula for complex scalars. -/
example (a b : ℂ) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((n : ℚ)⁻¹ • a) * NormedSpace.exp ((n : ℚ)⁻¹ • b)) ^ n)
      atTop (nhds (NormedSpace.exp (a + b))) :=
  tendsto_trotter_product a b

/-- Concrete scalar case: the limit for `2` and `3` is `Real.exp 5`. -/
example :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((n : ℚ)⁻¹ • (2 : ℝ)) *
        NormedSpace.exp ((n : ℚ)⁻¹ • (3 : ℝ))) ^ n)
      atTop (nhds (Real.exp 5)) := by
  have h := tendsto_trotter_product (2 : ℝ) (3 : ℝ)
  rw [show (2 : ℝ) + 3 = 5 by norm_num] at h
  rw [show NormedSpace.exp (5 : ℝ) = Real.exp 5 from
    (congrFun Real.exp_eq_exp_ℝ 5).symm] at h
  exact h

/-- Exactness for commuting scalars at `n = 3`. -/
example (a b : ℝ) :
    (NormedSpace.exp ((3 : ℚ)⁻¹ • a) * NormedSpace.exp ((3 : ℚ)⁻¹ • b)) ^ 3 =
      NormedSpace.exp (a + b) :=
  trotter_product_of_commute (Commute.all a b) (by norm_num)

/-- The one-step estimate, in its general form. -/
example (x y : ℝ) :
    ‖NormedSpace.exp x * NormedSpace.exp y - NormedSpace.exp (x + y)‖ ≤
      ‖x‖ * ‖y‖ + ‖x‖ ^ 2 * Real.exp ‖x‖ * Real.exp ‖y‖ +
        (1 + ‖x‖) * (‖y‖ ^ 2 * Real.exp ‖y‖) +
        (‖x‖ + ‖y‖) ^ 2 * Real.exp (‖x‖ + ‖y‖) :=
  norm_exp_mul_exp_sub_exp_add_le x y

/-- The exponential norm bound, in its general form. -/
example (x : ℝ) : ‖NormedSpace.exp x‖ ≤ Real.exp ‖x‖ :=
  norm_exp_le_exp_norm x

/-- The power-difference bound, in its general form. -/
example (X Y : ℝ) (n : ℕ) :
    ‖X ^ n - Y ^ n‖ ≤ (n : ℝ) * ‖X - Y‖ * (max (max ‖X‖ ‖Y‖) 1) ^ n :=
  norm_pow_sub_pow_le X Y n

#print axioms MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula.tendsto_trotter_product
#print axioms MathlibExt.Analysis.Normed.Algebra.TrotterProductFormula.trotter_product_of_commute

end MathlibExtTest.Analysis.Normed.Algebra.TrotterProductFormulaTests
