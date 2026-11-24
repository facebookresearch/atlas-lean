/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Set.Basic

/-!
# Observation-only policy conflict

Over an explicit execution model (a reachability predicate
over observation histories and states), no deterministic
observation-only policy can satisfy the necessary-action
specification when one history reaches two states whose
necessary action sets are disjoint.
-/

@[expose] public section

namespace Robotics.Information

/-- A deterministic policy's chosen action at one history
cannot lie in two disjoint sets. -/
private theorem action_not_mem_of_disjoint {O A S : Type*}
    (π : List O → A) {h : List O} {s₁ s₂ : S}
    (Req : S → Set A)
    (hdisj : Disjoint (Req s₁) (Req s₂)) :
    ¬ (π h ∈ Req s₁ ∧ π h ∈ Req s₂) := by
  intro hmem
  exact (Set.mem_empty_iff_false _).mp
    (hdisj.le_bot (Set.mem_inter hmem.1 hmem.2))

/-- Observation-only policy impossibility over an explicit
execution model. Reachability `Reaches h s` records that an
admissible execution can end in state `s` after producing
observation history `h`. A policy `π` satisfies the
necessary-action specification if, at every reachable
ending, its chosen action lies in that state's necessary
action set `Req s`. If one history reaches two states
whose necessary action sets are disjoint, no observation-
only policy satisfies the specification: its single
action at that history cannot be necessary at both
endings. -/
theorem not_satisfies_of_reachable_conflict {O A S : Type*}
    (π : List O → A) (Reaches : List O → S → Prop)
    {h : List O} {s₁ s₂ : S}
    (hr₁ : Reaches h s₁) (hr₂ : Reaches h s₂)
    (Req : S → Set A)
    (hdisj : Disjoint (Req s₁) (Req s₂)) :
    ¬ (∀ h' s, Reaches h' s → π h' ∈ Req s) := by
  intro hspec
  exact action_not_mem_of_disjoint π Req hdisj
    ⟨hspec h s₁ hr₁, hspec h s₂ hr₂⟩

end Robotics.Information
