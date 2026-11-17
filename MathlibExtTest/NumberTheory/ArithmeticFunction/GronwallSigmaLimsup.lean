/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsup

/-!
# Tests for Gronwall's theorem on the maximal order of `σ`
-/

@[expose] public section

example : Filter.limsup (fun n : ℕ => ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
      ((n : ℝ) * Real.log (Real.log n))) Filter.atTop =
    Real.exp Real.eulerMascheroniConstant :=
  MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted.gronwall_sigma_limsup
