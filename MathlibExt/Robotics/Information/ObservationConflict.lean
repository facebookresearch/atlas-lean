/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Data.Set.Basic

/-!
# Observation-only policy conflict

A deterministic policy that sees only an observation
history cannot meet disjoint necessary-action requirements
at two states reached after the same history: its single
chosen action cannot lie in both sets.
-/

@[expose] public section

namespace Robotics.Information

/-- Observation-only policy conflict. A deterministic
policy `π` maps observation histories to actions. If two
admissible executions end in states `s₁` and `s₂` after
the *same* observation history, and the sets of actions
necessary at those states are disjoint, then `π` cannot
meet the necessary-action requirement at both endings:
its single chosen action cannot lie in both sets. -/
theorem policyAction_not_mem_of_disjoint {O A S : Type*}
    (π : List O → A) {h : List O} {s₁ s₂ : S}
    (Req : S → Set A)
    (hdisj : Disjoint (Req s₁) (Req s₂)) :
    ¬ (π h ∈ Req s₁ ∧ π h ∈ Req s₂) := by
  intro hmem
  exact (Set.mem_empty_iff_false _).mp
    (hdisj.le_bot (Set.mem_inter hmem.1 hmem.2))

end Robotics.Information
