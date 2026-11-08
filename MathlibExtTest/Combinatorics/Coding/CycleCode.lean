/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Coding.CycleCode
import Mathlib.Data.Fin.VecNotation

namespace MathlibExtTest.Combinatorics.Coding.CycleCode

open MathlibExt.Combinatorics.Coding.CycleGraphCode

/-- The populated two-dimensional running example in the retained Tandon source,
stated against the generic modular predicate at modulus seven. -/
def tenWordCode : Finset (Fin 2 → ZMod 7) :=
  {![2, 2], ![2, 4], ![4, 2], ![4, 4], ![0, 1],
    ![0, 3], ![6, 5], ![1, 6], ![3, 0], ![5, 0]}

theorem tenWordCode_card : tenWordCode.card = 10 := by decide

theorem tenWordCode_isCode : IsCycleCode 7 tenWordCode := by
  unfold IsCycleCode
  decide

theorem actual_code_generic_rate :
    ENNReal.rpow 10 ((2 : ℝ)⁻¹) ≤ shannonCapacityCycle 7 :=
  cycleConstruction_implies_lowerBound 7 2 10 (by decide)
    ⟨tenWordCode, tenWordCode_isCode, tenWordCode_card⟩

theorem modular_wraparound_is_confusable :
    ¬IsCycleCode 7 ({fun _ ↦ 0, fun _ ↦ 6} : Finset (Fin 1 → ZMod 7)) := by
  unfold IsCycleCode
  decide

example : Finite (CycleCode 7 200) := cycleCode_finite 7 200
example : Finite (CycleCode 11 174) := cycleCode_finite 11 174
example : Finite (CycleCode 13 432) := cycleCode_finite 13 432
example : Finite (CycleCode 15 4096) := cycleCode_finite 15 4096
example : Finite (CycleCode 19 16384) := cycleCode_finite 19 16384
example : Finite (CycleCode 21 4096) := cycleCode_finite 21 4096
example : Finite (CycleCode 23 2048) := cycleCode_finite 23 2048

end MathlibExtTest.Combinatorics.Coding.CycleCode
