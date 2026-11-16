/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.SlackForm

@[expose] public section

/-- The zero system: every nonnegative vector is a solution with slack 0. -/
example : IsSolution (m := 1) (n := 1) (fun _ _ => (0 : ℚ)) (fun _ => 0)
    (fun _ => 0) := by
  simp [IsSolution]

end
