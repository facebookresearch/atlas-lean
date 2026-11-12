/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.WeightedIntervalScheduling

/-- Boundary check: the optimum of the empty family is `0`, and
the exchange identity instantiates with `S = ∅`. -/
example : wisOpt ∅ = 0 ∧
    wisOpt (insert (0, 1, 5) ∅) =
      max (wisOpt ∅) ((0, 1, 5).2.2 +
        wisOpt ((∅ : Finset (ℕ × ℕ × ℕ)).filter (fun a => a.2.1 ≤ (0, 1, 5).1 ∨ (0, 1, 5).2.1 ≤ a.1))) :=
  ⟨by decide, wisOpt_insert _ _ (by simp)⟩
