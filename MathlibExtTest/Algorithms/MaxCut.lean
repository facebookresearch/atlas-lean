/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algorithms.MaxCut
import Mathlib.Tactic.NormNum

@[expose] public section

/-- Boundary check: the cut of the constant assignment is zero. -/
example (E : EdgeSet 2) (hE : ∀ e ∈ E, e.1 < e.2) :
    cutCount E (fun _ => true) = 0 := by
  simp [cutCount]

/-- The expected-cut identity instantiates at `n = 1` with the
empty edge set. -/
example : (∑ x : Fin 1 → Bool, cutCount (∅ : EdgeSet 1) x) =
    2 ^ (1 - 1) * (∅ : EdgeSet 1).card := by
  simpa using sum_cutCount (by norm_num) (∅ : EdgeSet 1) (by simp)
