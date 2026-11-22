/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv

/-!
# Tests for a monotone differentiable function with discontinuous derivative

The construction gives a function on `ℝ` that is differentiable everywhere
and monotone, but whose derivative is not continuous.
-/

-- The derivative at zero exists and equals 3.
example :
    deriv MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotoneDiscontinuousDerivFn 0 = 3 :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_zero

-- Away from zero, the derivative is given by the explicit formula.
example (x : ℝ) (hx : x ≠ 0) :
    deriv MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotoneDiscontinuousDerivFn x =
      MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.derivativeFormula x :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_ne_zero x hx

-- The derivative is nonnegative everywhere.
example (x : ℝ) :
    0 ≤ deriv MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotoneDiscontinuousDerivFn x :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_nonneg x

-- The constructed function is differentiable everywhere.
example :
    ∀ x : ℝ,
      DifferentiableAt ℝ
        MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotoneDiscontinuousDerivFn x :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.differentiableAt_constructedFunction

-- The constructed function is monotone.
example :
    Monotone
      MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotoneDiscontinuousDerivFn :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotone_constructedFunction

-- Its derivative is not continuous.
example :
    ¬ Continuous
      (deriv MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotoneDiscontinuousDerivFn) :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_not_continuous

-- The original MA-ProofBench existence statement is proved.
example :
    ∃ f : ℝ → ℝ,
      Monotone f ∧
      (∀ x : ℝ, DifferentiableAt ℝ f x) ∧
      ¬ Continuous (deriv f) :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDerivWanted
    .exists_monotone_differentiable_not_continuous_deriv

#print axioms MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_zero
#print axioms MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_ne_zero
#print axioms MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.monotone_constructedFunction
#print axioms MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv.deriv_not_continuous
#print axioms MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDerivWanted.exists_monotone_differentiable_not_continuous_deriv
