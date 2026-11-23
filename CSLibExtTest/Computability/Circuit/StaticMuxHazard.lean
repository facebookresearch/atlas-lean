/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Circuit.StaticMuxHazard
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Static mux hazard tests

Concrete checks of the public API: the glitch at `t = 3 / 2` for
`d1 = 2`, `d2 = 1` and `dor = 0`, its consensus repair, the glitch
interval endpoints, and the no-glitch case.
-/

@[expose] public section

namespace CSLibExt.Computability.Circuit.StaticMuxHazard

/-- The concrete example packages the glitch and its repair. -/
example : muxTrace 2 1 0 (3 / 2) = false := muxTrace_example.2.1

/-- The repaired trace is true at the glitch instant. -/
example : repairedTrace 2 1 0 (3 / 2) = true := muxTrace_example.2.2.2

/-- The repaired trace is true at an arbitrary time. -/
example : repairedTrace 2 1 0 (7 / 3) = true := repairedTrace_eq_true 2 1 0 (7 / 3)

/-- The left endpoint of the glitch interval is included. -/
example : muxTrace 2 1 0 1 = false := by
  apply muxTrace_eq_false_of_mem_glitch
  · norm_num
  · rw [Set.mem_Ico]
    constructor <;> norm_num

/-- The right endpoint of the glitch interval is excluded. -/
example : muxTrace 2 1 0 2 = true := muxTrace_eq_true_of_ge 2 1 0 2 (by norm_num)

/-- Before the glitch interval, the output is true. -/
example : muxTrace 2 1 0 0 = true := muxTrace_eq_true_of_lt 2 1 0 0 (by norm_num)

/-- After the glitch interval, the output is true. -/
example : muxTrace 2 1 0 3 = true := muxTrace_eq_true_of_ge 2 1 0 3 (by norm_num)

/-- Before time zero, the output takes its steady initialization value. -/
example : muxTrace 2 1 0 (-1) = true :=
  muxTrace_eq_true_of_neg 2 1 0 (-1) (by norm_num)

/-- With `d1 ≤ d2` there is no glitch, even inside the former window. -/
example : muxTrace 1 2 0 (3 / 2) = true := muxTrace_eq_true_of_le 1 2 0 (3 / 2) (by norm_num)

/-- A false output occurs for `d1 = 2`, `d2 = 1`, and not otherwise. -/
example : (∃ t : ℝ, muxTrace 2 1 0 t = false) ∧
    ¬ (∃ t : ℝ, muxTrace 1 2 0 t = false) := by
  constructor
  · exact (exists_muxTrace_eq_false_iff 2 1 0).2 (by norm_num)
  · intro h
    have h' := (exists_muxTrace_eq_false_iff 1 2 0).1 h
    norm_num at h'

/-- Static values: the multiplexer and its consensus repair agree. -/
example : muxFunction true true false = true ∧
    muxFunction false false true = true ∧
    consensusFunction true true false = true ∧
    consensusFunction false false true = true ∧
    muxFunction false true true = true ∧
    consensusFunction true false true = muxFunction true false true :=
  ⟨rfl, rfl, rfl, rfl, muxFunction_true_true false,
    consensusFunction_eq_muxFunction true false true⟩

end CSLibExt.Computability.Circuit.StaticMuxHazard
