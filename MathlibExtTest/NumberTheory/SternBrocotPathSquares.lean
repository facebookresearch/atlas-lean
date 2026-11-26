/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Field.Rat
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.SternBrocotPathSquares

/-! # Tests for sums of two squares from Stern–Brocot paths -/

namespace MetaMathlibExt

local notation "R" => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ)
local notation "L" => (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ)

-- The shortest palindrome [2; 2] gives the single right move and coordinates (1, 2).
example :
    let M := R
    5 = (M.transpose.mulVec ![1, 1] 0) ^ 2 + (M.transpose.mulVec ![1, 1] 1) ^ 2 := by
  refine sq_add_sq_of_sternBrocot_path (p := 5) (x₀ := 2)
    (by decide) (by decide) (by decide) (by decide) (by decide) 0 (fun _ => 2)
    (fun _ _ => by decide) ?_
  change (5 / 2 : ℚ) = ([2, 2] : List ℕ).foldr (fun a acc => (a : ℚ) + acc⁻¹) 0
  norm_num [List.bind_eq_flatMap, List.pure_def]

-- The odd endpoint for [2; 1, 1, 2] gives coordinates (3, 2).
example :
    let M := R * L
    13 = (M.transpose.mulVec ![1, 1] 0) ^ 2 + (M.transpose.mulVec ![1, 1] 1) ^ 2 := by
  refine sq_add_sq_of_sternBrocot_path (p := 13) (x₀ := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) 1
    (fun i => if i = 1 then 1 else 2) (by intro i _; split <;> decide) ?_
  change (13 / 5 : ℚ) = ([2, 1, 1, 2] : List ℕ).foldr (fun a acc => (a : ℚ) + acc⁻¹) 0
  norm_num [List.bind_eq_flatMap, List.pure_def]

-- The even endpoint for [2; 1, 2, 2, 1, 2] gives coordinates (3, 8).
example :
    let M := R * L * R ^ 2
    73 = (M.transpose.mulVec ![1, 1] 0) ^ 2 + (M.transpose.mulVec ![1, 1] 1) ^ 2 := by
  refine sq_add_sq_of_sternBrocot_path (p := 73) (x₀ := 27)
    (by decide) (by decide) (by decide) (by decide) (by decide) 2
    (fun i => if i = 1 then 1 else 2) (by intro i _; split <;> decide) ?_
  change (73 / 27 : ℚ) = ([2, 1, 2, 2, 1, 2] : List ℕ).foldr (fun a acc => (a : ℚ) + acc⁻¹) 0
  norm_num [List.bind_eq_flatMap, List.pure_def]

end MetaMathlibExt
