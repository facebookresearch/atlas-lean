/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum.GCD
import MathlibExt.NumberTheory.NicomacheanTranslations

/-! # Tests for the Nicomachean defect and progression factor -/

open MetaMathlibExt

-- The empty list has zero defect.
example : nicomacheanNu ([] : List ℚ) = 0 := by simp [nicomacheanNu]

-- At Q = 3 the smaller entry of the constructed pair reduces from 6/21 to 2/7.
example : nicomacheanNu ([6 / 21, 30 / 21] : List ℚ) = 0 ∧ (6 / 21 : ℚ).den = 7 := by
  norm_num [nicomacheanNu]

-- At length one, the progression factor is independent of its step.
example (s a : ℚ) : nicomacheanAlpha 1 s a = 2 + a - a ^ 2 := by
  simp [nicomacheanAlpha]
