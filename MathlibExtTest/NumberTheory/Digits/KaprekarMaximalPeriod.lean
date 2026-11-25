/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.KaprekarMaximalPeriod

open Function MetaMathlibExt

example : kaprekarFourDigitStep 5 (3, 1) = (3, 1) := by
  simp [kaprekarFourDigitStep, List.insertionSort_cons, List.orderedInsert_cons]

example : (3, 1) ∈ kaprekarFourDigitStates 7 ∧ (7, 1) ∉ kaprekarFourDigitStates 7 := by
  simp [kaprekarFourDigitStates]

example : ¬ ∃ d ∈ kaprekarFourDigitStates 5, minimalPeriod (kaprekarFourDigitStep 5) d = 2 := by
  intro h
  have hbase := ((kaprekar_minimalPeriod_le_and_eq_iff 5 (by decide) (by decide)).2.mp h).1
  omega

example : ∃ d ∈ kaprekarFourDigitStates 7, minimalPeriod (kaprekarFourDigitStep 7) d = 3 :=
  (kaprekar_minimalPeriod_le_and_eq_iff 7 (by decide) (by decide)).2.mpr
    ⟨by decide, by decide, projectiveOrderTwo_examples.1⟩

example : ¬ ∃ d ∈ kaprekarFourDigitStates 17, minimalPeriod (kaprekarFourDigitStep 17) d = 8 := by
  intro h
  have horder := ((kaprekar_minimalPeriod_le_and_eq_iff 17 (by decide) (by decide)).2.mp h).2.2
  have hfour := projectiveOrderTwo_examples.2.2.2
  omega
