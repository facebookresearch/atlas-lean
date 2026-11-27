/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TruncatedLogDiscriminantPrimePower

/-! # Tests for truncated logarithmic discriminants at prime powers -/

open MetaMathlibExt

-- The smallest eligible prime and positive exponent.
example : ¬ IsSquare (truncatedLogPolynomial 5).discr :=
  (discr_truncatedLog_prime_power (p := 5) (e := 1) (by decide) (by decide) (by decide)).1
    (by decide)

-- The first even exponent gives both directions of the nonsquare criterion.
example : (¬ IsSquare (truncatedLogPolynomial 25).discr) ↔
    ¬ IsSquare (truncatedLogResultantProduct 25 : ℚ) :=
  (discr_truncatedLog_prime_power (p := 5) (e := 2) (by decide) (by decide) (by decide)).2
    (by decide)

example : ¬ IsSquare (truncatedLogPolynomial 125).discr :=
  (discr_truncatedLog_prime_power (p := 5) (e := 3) (by decide) (by decide) (by decide)).1
    (by decide)
