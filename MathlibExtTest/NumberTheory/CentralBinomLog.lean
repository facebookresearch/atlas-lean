/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CentralBinomLog

/-! # Tests for `MathlibExt.NumberTheory.CentralBinomLog` -/

namespace MathlibExtTest.NumberTheory.CentralBinomLog

open MetaMathlibExt

-- At `n = 2`: `log 6 = log 4! - 2 log 2!`.
example : Real.log 6 = Real.log 24 - 2 * Real.log 2 := by
  have h := log_centralBinom 2
  norm_num [Nat.centralBinom, Nat.choose, Nat.factorial] at h
  exact h

end MathlibExtTest.NumberTheory.CentralBinomLog
