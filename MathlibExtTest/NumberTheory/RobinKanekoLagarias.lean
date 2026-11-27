/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RobinKanekoLagarias

/-! # Tests for `MathlibExt.NumberTheory.RobinKanekoLagarias` -/

namespace MathlibExtTest.RobinKanekoLagarias

open Real

/-- Robin's inequality implies the Kaneko–Lagarias inequality, applied with
its hypothesis passed by name. -/
example (n : ℕ)
    (h : (ArithmeticFunction.sigma 1 n : ℝ) <
      exp eulerMascheroniConstant * n * log (log n)) :
    (ArithmeticFunction.sigma 1 n : ℝ) < exp (harmonic n : ℝ) * log (harmonic n : ℝ) :=
  MetaMathlibExt.kaneko_lagarias_of_robin n (h := h)

end MathlibExtTest.RobinKanekoLagarias
