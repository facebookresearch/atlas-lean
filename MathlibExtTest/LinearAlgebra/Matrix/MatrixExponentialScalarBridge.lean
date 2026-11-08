/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTrace
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

/-!
# Matrix exponential scalar interoperability

A client of the determinant API can use `NormedSpace.exp` for both matrix and scalar arguments.
The scalar spelling bridge is imported directly from its providing module.
-/

namespace MatrixExponentialScalarBridgeTest

open MathlibExt.LinearAlgebra.Matrix.MatrixExpDetTraceWanted

private theorem matrix_exponential_scalar_bridge {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A) := by
  rw [matrix_det_exp_eq_exp_trace, Complex.exp_eq_exp_ℂ]

#print axioms matrix_exponential_scalar_bridge

end MatrixExponentialScalarBridgeTest
