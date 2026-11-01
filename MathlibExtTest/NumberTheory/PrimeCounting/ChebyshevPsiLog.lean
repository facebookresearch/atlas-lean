/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ChebyshevPsiLog

/-!
# Tests for the logarithmically weighted Chebyshev function
-/

@[expose] public section

open Finset ArithmeticFunction

namespace ChebyshevPsiLogTest

/-- At `x = y` both sides vanish. -/
example (x : ℝ) (hx : 1 ≤ x) : Chebyshev.psi x * Real.log (x / x) ≤
    (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n)) - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n) :=
  Chebyshev.psi_mul_log_div_le_sub hx le_rfl

/-- From `w = 1` (where `ψ₁(1) = 0`): `ψ₁(x) ≤ ψ(x) log x`. -/
example {x : ℝ} (hx : 1 ≤ x) : (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * Real.log (x / n)) ≤
    Chebyshev.psi x * Real.log x := by
  have h := Chebyshev.sub_le_psi_mul_log_div le_rfl hx
  simpa using h

end ChebyshevPsiLogTest
