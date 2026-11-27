/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.DeterministicFiniteHorizon
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Tests for backward induction in deterministic finite-horizon control

Concrete checks for
`CSLibExt/Algorithms/Lean/DynamicProgramming/DeterministicFiniteHorizon.lean`:

* a two-stage problem on the infinite state type `ℕ` with stage-dependent admissible sets, where
  the myopically cheapest first action is not optimal: its backward-induction values, an optimal
  sequence, the costlier myopic sequence, and the matching shortest path;
* the horizon `N = 0`, where the value is the terminal cost;
* a one-stage problem with two parallel arcs of different lengths;
* acyclicity of the stage-indexed graph.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.DeterministicFiniteHorizon.Tests

open ControlProblem

/-! ## A two-stage detour on `ℕ` -/

/-- Two stages on states `ℕ`: action `true` moves `s ↦ s + 1` at cost `1`, action `false` stays
at cost `2`; only stage `0` allows moving, and the terminal cost is `0` at state `0` and `10`
elsewhere. -/
private def detour : ControlProblem 2 ℕ Bool where
  admissible t _ := if t = 0 then {false, true} else {false}
  admissible_nonempty t _ := by split <;> simp
  transition _ s a := if a then s + 1 else s
  cost _ _ a := if a then 1 else 2
  terminalCost s := if s = 0 then 0 else 10

@[simp] private theorem detour_admissible_zero (s : ℕ) :
    detour.admissible 0 s = {false, true} := rfl

@[simp] private theorem detour_admissible_one (s : ℕ) : detour.admissible 1 s = {false} := rfl

@[simp] private theorem detour_transition (t : Fin 2) (s : ℕ) (a : Bool) :
    detour.transition t s a = if a then s + 1 else s := rfl

@[simp] private theorem detour_cost (t : Fin 2) (s : ℕ) (a : Bool) :
    detour.cost t s a = if a then 1 else 2 := rfl

@[simp] private theorem detour_terminalCost (s : ℕ) :
    detour.terminalCost s = if s = 0 then 0 else 10 := rfl

@[simp] private theorem detour_value_two : detour.backwardValue 2 = detour.terminalCost :=
  detour.backwardValue_last

@[simp] private theorem detour_value_one (s : ℕ) :
    detour.backwardValue 1 s = 2 + if s = 0 then 0 else 10 := by
  have h := detour.backwardValue_castSucc 1 s
  simp only [Fin.castSucc_one, Fin.succ_one_eq_two] at h
  simp [h]

private theorem detour_value_zero_zero : detour.backwardValue 0 0 = 4 := by
  have h := detour.backwardValue_castSucc 0 0
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h
  simp [h]
  norm_num

/-- The optimal sequence stays twice. -/
private def stayStates : Fin 3 → ℕ := fun _ => 0

private def stayActions : Fin 2 → Bool := fun _ => false

/-- The myopic sequence moves first, the cheaper first step. -/
private def moveStates : Fin 3 → ℕ := ![0, 1, 1]

private def moveActions : Fin 2 → Bool := ![true, false]

private theorem stay_admissible : detour.IsAdmissibleSequence 0 0 stayStates stayActions :=
  ⟨rfl, Fin.forall_fin_two.mpr ⟨fun _ => by simp [stayStates, stayActions],
    fun _ => by simp [stayStates, stayActions]⟩⟩

private theorem stay_totalCost : detour.totalCost 0 stayStates stayActions = 4 := by
  simp [totalCost, stayStates, stayActions]
  norm_num

private theorem move_admissible : detour.IsAdmissibleSequence 0 0 moveStates moveActions :=
  ⟨rfl, Fin.forall_fin_two.mpr ⟨fun _ => by simp [moveStates, moveActions],
    fun _ => by simp [moveStates, moveActions]⟩⟩

private theorem move_totalCost : detour.totalCost 0 moveStates moveActions = 13 := by
  simp [totalCost, moveStates, moveActions, Fin.sum_univ_two]
  norm_num

/-- The minimum total cost from state `0` at stage `0` is `4`. -/
example :
    IsLeast {J | ∃ x u, detour.IsAdmissibleSequence 0 0 x u ∧ detour.totalCost 0 x u = J} 4 := by
  simpa [detour_value_zero_zero] using (detour.backwardValue_spec 0 0).1

/-- The staying sequence is optimal. -/
example : detour.totalCost 0 stayStates stayActions = detour.backwardValue 0 0 := by
  rw [stay_totalCost, detour_value_zero_zero]

/-- The myopic sequence is admissible but costs more than the value. -/
example : detour.backwardValue 0 0 < detour.totalCost 0 moveStates moveActions := by
  rw [move_totalCost, detour_value_zero_zero]
  norm_num

/-- The lower bound of `backward_induction` applied to the myopic sequence. -/
example : detour.backwardValue 0 0 ≤ 13 :=
  (detour.backwardValue_spec 0 0).1.2 ⟨moveStates, moveActions, move_admissible,
    move_totalCost⟩

/-- The minimizing clause of `backward_induction` recovers the cost of the staying sequence. -/
example : detour.totalCost 0 stayStates stayActions = detour.backwardValue 0 0 := by
  refine (detour.backwardValue_spec 0 0).2.1 _ _ stay_admissible
    (Fin.forall_fin_two.mpr ⟨fun _ a ha => ?_, fun _ a ha => ?_⟩)
  · simp only [Fin.castSucc_zero, detour_admissible_zero, Finset.mem_insert,
      Finset.mem_singleton] at ha
    rcases ha with rfl | rfl <;> simp [stayStates, stayActions]
    norm_num
  · simp only [Fin.castSucc_one, detour_admissible_one, Finset.mem_singleton] at ha
    simp [ha, stayStates, stayActions]

/-- The arcs `(0, 0) → (1, 0) → (2, 0) → sink` of the staying actions. -/
private def stayArc₀ : (StageVertex.node 0 0 : detour.StageVertex) ⟶ StageVertex.node 1 0 :=
  StageArc.step 0 0 false (by simp)

private def stayArc₁ : (StageVertex.node 1 0 : detour.StageVertex) ⟶ StageVertex.node 2 0 :=
  StageArc.step 1 0 false (by simp)

private def stayArc₂ : (StageVertex.node 2 0 : detour.StageVertex) ⟶ StageVertex.sink :=
  StageArc.exit 0

@[simp] private theorem stayArc₀_length : detour.stageArcLength stayArc₀ = 2 := rfl

@[simp] private theorem stayArc₁_length : detour.stageArcLength stayArc₁ = 2 := rfl

@[simp] private theorem stayArc₂_length : detour.stageArcLength stayArc₂ = 0 := rfl

/-- The path of the staying actions has length `4`. -/
example : (((Quiver.Path.nil.cons stayArc₀).cons stayArc₁).cons stayArc₂).addWeight
    detour.stageArcLength = 4 := by
  simp
  norm_num

/-- The shortest-path distance from `(0, 0)` to the sink is `4`. -/
example : IsLeast (Set.range fun p : Quiver.Path (V := detour.StageVertex) (StageVertex.node 0 0)
    StageVertex.sink => p.addWeight detour.stageArcLength) 4 := by
  simpa [detour_value_zero_zero] using (detour.backwardValue_spec 0 0).2.2

/-! ## The horizon `N = 0` -/

/-- A problem with no stages: only the terminal cost `g s = s` counts. -/
private def noStages : ControlProblem 0 ℕ Bool where
  admissible t := t.elim0
  admissible_nonempty t := t.elim0
  transition t := t.elim0
  cost t := t.elim0
  terminalCost s := s

private theorem noStages_value (s : ℕ) : noStages.backwardValue 0 s = s :=
  congrFun noStages.backwardValue_last s

example (s : ℕ) :
    IsLeast {J | ∃ x u, noStages.IsAdmissibleSequence 0 s x u ∧ noStages.totalCost 0 x u = J}
      s := by
  simpa [noStages_value] using (noStages.backwardValue_spec 0 s).1

example (s : ℕ) : noStages.totalCost 0 (fun _ => s) Fin.elim0 = s :=
  noStages.totalCost_last (fun _ => s) Fin.elim0

/-! ## Parallel arcs -/

/-- One stage on a single state with two actions of costs `3` and `5` and terminal cost `0`; the
two actions give two parallel arcs of the stage-indexed graph. -/
private def parallel : ControlProblem 1 Unit Bool where
  admissible _ _ := {false, true}
  admissible_nonempty _ _ := by simp
  transition _ _ _ := ()
  cost _ _ a := if a then 5 else 3
  terminalCost _ := 0

@[simp] private theorem parallel_admissible (t : Fin 1) (s : Unit) :
    parallel.admissible t s = {false, true} := rfl

@[simp] private theorem parallel_cost (t : Fin 1) (s : Unit) (a : Bool) :
    parallel.cost t s a = if a then 5 else 3 := rfl

@[simp] private theorem parallel_terminalCost (s : Unit) : parallel.terminalCost s = 0 := rfl

@[simp] private theorem parallel_value_one : parallel.backwardValue 1 = parallel.terminalCost :=
  parallel.backwardValue_last

private theorem parallel_value : parallel.backwardValue 0 () = 3 := by
  have h := parallel.backwardValue_castSucc 0 ()
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h
  simp [h]
  norm_num

private def parallelPath (a : Bool) :
    Quiver.Path (V := parallel.StageVertex) (StageVertex.node 0 ()) StageVertex.sink :=
  (Quiver.Hom.toPath (V := parallel.StageVertex) (StageArc.step 0 () a (by simp))).comp
    (Quiver.Hom.toPath (V := parallel.StageVertex) (StageArc.exit ()))

example : (parallelPath false).addWeight parallel.stageArcLength = 3 := by
  simp [parallelPath, Quiver.Hom.toPath, stageArcLength]

example : (parallelPath true).addWeight parallel.stageArcLength = 5 := by
  simp [parallelPath, Quiver.Hom.toPath, stageArcLength]

/-- The shortest-path distance takes the shorter parallel arc. -/
example : IsLeast (Set.range fun p : Quiver.Path (V := parallel.StageVertex) (StageVertex.node 0 ())
    StageVertex.sink => p.addWeight parallel.stageArcLength) 3 := by
  simpa [parallel_value] using (parallel.backwardValue_spec 0 ()).2.2

/-! ## Acyclicity -/

example (p : Quiver.Path (V := detour.StageVertex) (StageVertex.node 1 5) (StageVertex.node 1 5)) :
    p = Quiver.Path.nil :=
  detour.stageArc_acyclic p

example (p : Quiver.Path (V := parallel.StageVertex) StageVertex.sink StageVertex.sink) :
    p.length = 0 := by
  rw [parallel.stageArc_acyclic p, Quiver.Path.length_nil]

end Cslib.Algorithms.Lean.DeterministicFiniteHorizon.Tests
