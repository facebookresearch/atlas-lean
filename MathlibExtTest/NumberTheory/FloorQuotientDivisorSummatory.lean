/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FloorQuotientDivisorSummatory

open MetaMathlibExt

example : (floorQuotientOddCount 0 : ℤ) = 0 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

example : (floorQuotientOddCount 1 : ℤ) = 1 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

example : (floorQuotientOddCount 6 : ℤ) = 4 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide

example : (floorQuotientOddCount 7 : ℤ) = 6 := by
  rw [floorQuotientOddCount_eq_divisor_summatory_sub]
  decide
