/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.PivotTermination

@[expose] public section

/-- Counting up to a cap reaches its fixed point. -/
example : ∃ k ≤ 4, (fun x : ℕ => if x < 3 then x + 1 else x)^[k + 1] 0
    = (fun x : ℕ => if x < 3 then x + 1 else x)^[k] 0 :=
  iterate_fixed_of_potential (fun x : ℕ => if x < 3 then x + 1 else x)
    (fun x => min x 3) 3
    (fun s => Nat.min_le_right s 3)
    (fun s hs => by
      by_cases h : s < 3
      · simp only [h, if_true]
        omega
      · simp only [h, if_false] at hs
        exact absurd rfl hs) 0

end
