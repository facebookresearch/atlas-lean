/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.ContinuousTuranGrid
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The lower estimate applies already at the minimum row count.
example :
    (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => opx n (({-3, 0, 4} : Set ℝ) ×ˢ ({0, 1, 7} : Set ℝ))) := by
  simpa using (opx_grid_three_columns_isTheta
    (X := {-3, 0, 4}) (Y := {0, 1, 7}) (by norm_num) (by norm_num)).2

-- Adding a fourth, irregularly spaced row still gives the same upper exponent.
example :
    (fun n : ℕ => opx n (({-3, 0, 4} : Set ℝ) ×ˢ ({0, 1, 7, 9} : Set ℝ))) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (5 / 3 : ℝ)) := by
  simpa using (opx_grid_three_columns_isTheta
    (X := {-3, 0, 4}) (Y := {0, 1, 7, 9}) (by norm_num) (by norm_num)).1
