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

-- The original MA-ProofBench existence statement is proved.
example :
    ∃ f : ℝ → ℝ,
      Monotone f ∧
      (∀ x : ℝ, DifferentiableAt ℝ f x) ∧
      ¬ Continuous (deriv f) :=
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDerivWanted.exists_monotone_differentiable_not_continuous_deriv

-- Inspect the axioms of the public existential theorem.
#print axioms
  MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDerivWanted.exists_monotone_differentiable_not_continuous_deriv
