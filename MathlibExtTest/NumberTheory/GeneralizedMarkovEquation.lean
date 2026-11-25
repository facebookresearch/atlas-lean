/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.GeneralizedMarkovEquation

open MetaMathlibExt

-- At k = 0, the change of variables triples each coordinate.
example (a b c : ℚ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c) :
    (3 * a) ^ 2 + (3 * b) ^ 2 + (3 * c) ^ 2 = (3 * a) * (3 * b) * (3 * c) := by
  simpa using (genMarkov_iff_genSecondMarkov 0 a b c).mp (by simpa using h)

-- Gyoda and Maruyama's Example 2.5 sends (9, 9, 22) back to a nonintegral triple.
example :
    let k : ℕ := 4
    let a : ℚ := 13 / 15
    let c : ℚ := 26 / 15
    a ^ 2 + a ^ 2 + c ^ 2 + k * (a * c + c * a + a * a) = (3 + 3 * k) * a * a * c := by
  intro k a c
  apply (genMarkov_iff_genSecondMarkov k a a c).mpr
  norm_num [k, a, c]
