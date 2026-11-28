/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RemainderSetBoundsPrimeCounting

open MetaMathlibExt

-- The lower endpoint includes the first prime.
example : (1 : ℝ) ≤ 13 / 10 * 2 / Real.log 2 := by
  have h := primeCounting_le_thirteen_tenths (n := 2) (by decide)
  simpa only [show Nat.primeCounting 2 = 1 by decide, Nat.cast_one, Nat.cast_ofNat] using h

-- A prime in the finite range contributes to its own count.
set_option maxRecDepth 4096 in
example : (30 : ℝ) ≤ 13 / 10 * 113 / Real.log 113 := by
  have h := primeCounting_le_thirteen_tenths (n := 113) (by decide)
  simpa only [show Nat.primeCounting 113 = 30 by decide +kernel, Nat.cast_ofNat] using h

-- Check both sides of the transition from finite verification to the analytic estimate.
example : (Nat.primeCounting 65535 : ℝ) ≤ 13 / 10 * 65535 / Real.log 65535 :=
  primeCounting_le_thirteen_tenths (n := 65535) (by decide)

example : (Nat.primeCounting 65536 : ℝ) ≤ 13 / 10 * 65536 / Real.log 65536 :=
  primeCounting_le_thirteen_tenths (n := 65536) (by decide)
