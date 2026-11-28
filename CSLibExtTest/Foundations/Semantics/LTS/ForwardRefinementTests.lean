/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Foundations.Semantics.LTS.ForwardRefinement

/-! # Regression tests for data refinement -/

set_option autoImplicit false

namespace CSLibExtTest.Foundations.Semantics.LTS.ForwardRefinement

open Cslib

private abbrev Label := Bool × Bool × Bool

-- The operation flips the bit and returns its old value. The invariant excludes `none`.
private def flip (b : Bool) : Label := (true, true, b)

private def rejected : Label := (false, true, false)

private def concrete : LTS (Option Bool) Label where
  Tr s label t := match s with
    | some b => t = some (!b) ∧ label = flip b
    | none => t = none ∧ label = rejected

private def abstractBit : LTS Bool Label where
  Tr s label t := t = !s ∧ label = flip s

private def invariant : Set (Option Bool) := {s | ∃ b, s = some b}

private def concreteInit : Set (Option Bool) := {some false}

private def abstractInit : Set Bool := {false}

private def refinement :
    LTS.ForwardRefinement concrete abstractBit concreteInit abstractInit invariant where
  mapState s := s.val.getD false
  initial_mem s hs := by
    change s = some false at hs
    exact ⟨false, hs⟩
  initial_map s hs := by
    change s = some false at hs
    subst s
    rfl
  step_mem := by
    rintro s t label ⟨b, rfl⟩ h
    exact ⟨!b, h.1⟩
  step_map := by
    rintro s t label ⟨b, rfl⟩ h
    change t = some (!b) ∧ label = flip b at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

private theorem concrete_two_steps :
    concrete.Execution (some false) [flip false, flip true] (some false)
      [some false, some true, some false] :=
  .stepL (s := some true) ⟨rfl, rfl⟩ (.stepL ⟨rfl, rfl⟩ (.refl (some false)))

-- The map preserves the intermediate state as well as the operation/argument/result labels.
example : abstractBit.Execution false [flip false, flip true] false [false, true, false] := by
  obtain ⟨_, _, h⟩ := refinement.map_execution concrete_two_steps ⟨false, rfl⟩
  exact h

example : [flip false, flip true] ∈ abstractBit.tracesFrom abstractInit :=
  refinement.tracesFrom_subset ⟨some false, rfl, some false, concrete_two_steps.to_mTr⟩

example : [] ∈ abstractBit.tracesFrom abstractInit :=
  refinement.tracesFrom_subset ⟨some false, rfl, some false, .refl⟩

-- The excluded state can emit a label with no matching abstract transition.
example : [rejected] ∈ concrete.traces none ∧ [rejected] ∉ abstractBit.traces false := by
  refine ⟨⟨none, .stepL ⟨rfl, rfl⟩ .refl⟩, ?_⟩
  rw [LTS.mem_traces_singleton_iff]
  rintro ⟨t, _, h⟩
  have hOp := congrArg Prod.fst h
  change false = true at hOp
  cases hOp

private def alternating : ℕ → Bool
  | 0 => false
  | n + 1 => !(alternating n)

private def concreteStream : ωSequence (Option Bool) := ⟨fun i => some (alternating i)⟩

private def labelStream : ωSequence Label := ⟨fun i => flip (alternating i)⟩

example : abstractBit.OmegaExecution (⟨alternating⟩ : ωSequence Bool) labelStream := by
  have hc : concrete.OmegaExecution concreteStream labelStream := fun _ => ⟨rfl, rfl⟩
  obtain ⟨_, _, h⟩ := refinement.map_initial_omegaExecution hc (by rfl)
  exact h

end CSLibExtTest.Foundations.Semantics.LTS.ForwardRefinement
