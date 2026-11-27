/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Chemistry.MineralProcessing.TwoProductFormula
import Mathlib.Tactic.NormNum

open Domains.Chemistry.MineralProcessing.TwoProductFormula

-- The identity also covers a concentrate grade below the tailings grade.
example : (1 : ℝ) / 4 = (5 / 8 - 3 / 4) / (1 / 4 - 3 / 4) ∧
    (1 : ℝ) * (1 / 4) / (4 * (5 / 8)) = (1 / 4) * (5 / 8 - 3 / 4) / ((5 / 8) * (1 / 4 - 3 / 4)) := by
  have h := two_product_formula 4 1 3 (5 / 8) (1 / 4) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨hy, hr⟩ := h.2.2.1 (by norm_num)
  exact ⟨hy, hr (by norm_num)⟩

-- Equal grades do not identify the split, including at the endpoints.
example (x : ℝ) (hx0 : 0 ≤ x) (hxF : x ≤ 3) :
    0 ≤ 3 - x ∧ 3 = x + (3 - x) ∧ 3 * (1 / 2) = x * (1 / 2) + (3 - x) * (1 / 2) := by
  have h := two_product_formula 3 1 2 (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (h.2.2.2 rfl).2.2 x hx0 hxF
