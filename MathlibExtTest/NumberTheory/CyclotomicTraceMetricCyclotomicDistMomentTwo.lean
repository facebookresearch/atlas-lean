/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CyclotomicTraceMetricCyclotomicDistMomentTwo
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the second moment of the trace distance on the cyclotomic box -/

namespace MathlibExtTest.NumberTheory.CyclotomicTraceMetricCyclotomicDistMomentTwo

open MetaMathlibExt

instance : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
  CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero 3 ℚ

-- At conductor three and radius one the second moment is `40 / 3`.
example : cyclotomicDistMoment 3 (CyclotomicField 3 ℚ) 1 2 = 40 / 3 := by
  rw [cyclotomicDistMoment_two Nat.prime_three 1]
  norm_num

-- At conductor two the cubic factor collapses to one.
example {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {2} ℚ K] (N : ℕ) :
    cyclotomicDistMoment 2 K N 2 = 2 / 3 * N * (N + 1) := by
  have h2 : ((2 : ℕ) : ℝ) ^ 3 - 2 * ((2 : ℕ) : ℝ) ^ 2 + 1 = 1 := by norm_num
  rw [cyclotomicDistMoment_two Nat.prime_two N, h2]
  ring

-- The second moment vanishes on the radius-zero box.
example {p : ℕ} [NeZero p] {K : Type*} [Field K] [CharZero K]
    [IsCyclotomicExtension {p} ℚ K] (hp : p.Prime) :
    cyclotomicDistMoment p K 0 2 = 0 := by
  rw [cyclotomicDistMoment_two hp 0]
  norm_num

end MathlibExtTest.NumberTheory.CyclotomicTraceMetricCyclotomicDistMomentTwo
