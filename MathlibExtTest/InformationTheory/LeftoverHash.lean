/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.LeftoverHash
import Mathlib.Tactic.NormNum

@[expose] public section

/-- The uniform distribution on two points has collision probability at most `1/2`. -/
example : ∑ x : Fin 2, ((1 / 2 : ℝ)) ^ 2 ≤ 1 / 2 :=
  collision_le_of_le (fun _ => 1 / 2) (fun _ => by norm_num)
    (by simp) _ (fun _ => le_refl _)

end
