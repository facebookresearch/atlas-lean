/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SternBrocotSumTwoSquares

/-! # Tests for the columns of a Stern–Brocot matrix path -/

namespace MetaMathlibExt.continuedFraction_path_eq_convergents

local notation "R" => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℕ)
local notation "L" => (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) ℕ)

private def entry (q : ℕ → ℕ) (u v : ℕ) : ℕ → ℕ
  | 0 => u
  | 1 => v
  | k + 2 => q (k + 1) * entry q u v (k + 1) + entry q u v k

-- The odd endpoint updates the left column.
example (a b : ℕ) : R ^ a * L ^ b = !![b * a + 1, a; b, 1] := by
  let q : ℕ → ℕ := fun i => if i = 0 then a else b
  have h := continuedFraction_path_eq_convergents q (entry q 1 a) (entry q 0 1)
    rfl rfl (fun _ => rfl) rfl rfl (fun _ => rfl) 1
  simpa [List.range_succ, q, entry] using h

-- A zero middle coefficient skips the left move, and the even endpoint updates the right column.
example (a b : ℕ) : R ^ a * R ^ b = !![1, b + a; 0, 1] := by
  let q : ℕ → ℕ
    | 0 => a
    | 1 => 0
    | _ => b
  have h := continuedFraction_path_eq_convergents q (entry q 1 a) (entry q 0 1)
    rfl rfl (fun _ => rfl) rfl rfl (fun _ => rfl) 2
  simpa [List.range_succ, q, entry] using h

end MetaMathlibExt.continuedFraction_path_eq_convergents
