/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.MotionPlanning.Completeness
import Mathlib.MeasureTheory.Measure.Dirac.Basic

namespace CSLibExtTest.Planning.MotionPlanning

/-!
# Tests for planner completeness notions

* Test 1: the always-running planner is neither complete nor resolution
  complete (witnessed on a concrete solvable problem).
* Test 2 (conditional form): the oracle planner that never reports `noPath` is
  resolution complete, but not complete once an unsolvable instance exists.
* Test 3: the classical oracle planner is complete.
* Test 4: the oracle planner viewed as a random planner on a
  one-point space with Dirac measure is probabilistically complete; dually,
  the always-running random planner is not.
* Test 5: `#print axioms` for `Planner.Complete.resolutionComplete`.

## References

* LaValle, Planning Algorithms, Ch. 4-5.
* MIT 16.410 Lecture 15.
-/

open Cslib.Planning.MotionPlanning
open Classical

/-! ## Test 1: the always-running planner -/

/-- The planner that never answers. -/
def alwaysRunning {C : Type*} [TopologicalSpace C] : Planner C :=
  fun _ _ => PlannerAnswer.running

theorem alwaysRunning_not_complete {C : Type*} [TopologicalSpace C]
    (P : PathProblem C) : ¬ (alwaysRunning : Planner C).Complete := by
  rintro ⟨-, hTerm⟩
  obtain ⟨k, hk⟩ := hTerm P
  exact hk rfl

/-- A concrete solvable problem: trivial goal in `ℝ` with everything free. -/
def trivialProblem : PathProblem ℝ where
  free := Set.univ
  qI := 0
  qG := 0
  qI_mem := Set.mem_univ 0
  qG_mem := Set.mem_univ 0

theorem trivialProblem_solvable : PathProblem.Solvable ℝ trivialProblem :=
  ⟨Path.refl 0, fun _ => Set.mem_univ _⟩

theorem alwaysRunning_not_resolutionComplete :
    ¬ (alwaysRunning : Planner ℝ).ResolutionComplete := by
  rintro ⟨-, hRC⟩
  obtain ⟨k, γ, h⟩ := hRC trivialProblem trivialProblem_solvable
  simp [alwaysRunning] at h

/-! ## Test 2: strictness, conditional form -/

/-- Oracle that finds immediately on solvable problems but never reports `noPath`. -/
noncomputable def oracleRC {C : Type*} [TopologicalSpace C] : Planner C :=
  fun P _ => if h : PathProblem.Solvable C P then
    PlannerAnswer.found (Classical.choose h)
  else PlannerAnswer.running

theorem oracleRC_sound {C : Type*} [TopologicalSpace C] :
    (oracleRC : Planner C).Sound := by
  constructor
  · intro P k γ hEq
    simp only [oracleRC] at hEq
    by_cases hSolv : PathProblem.Solvable C P
    · rw [dite_eq_left hSolv] at hEq
      cases hEq
      exact Classical.choose_spec hSolv
    · rw [dite_eq_right hSolv] at hEq
      cases hEq
  · intro P k hEq
    simp only [oracleRC] at hEq
    by_cases hSolv : PathProblem.Solvable C P
    · rw [dite_eq_left hSolv] at hEq
      cases hEq
    · rw [dite_eq_right hSolv] at hEq
      cases hEq

theorem oracleRC_resolutionComplete {C : Type*} [TopologicalSpace C] :
    (oracleRC : Planner C).ResolutionComplete := by
  refine ⟨oracleRC_sound, fun P hSolv => ?_⟩
  refine ⟨0, Classical.choose hSolv, ?_⟩
  simp only [oracleRC, dite_eq_left hSolv]

theorem oracleRC_not_complete_of_unsolvable {C : Type*} [TopologicalSpace C]
    (P0 : PathProblem C) (h0 : ¬ PathProblem.Solvable C P0) :
    ¬ (oracleRC : Planner C).Complete := by
  rintro ⟨-, hTerm⟩
  obtain ⟨k, hk⟩ := hTerm P0
  simp only [oracleRC, dite_eq_right h0] at hk
  exact hk rfl

/-! ## Test 3: the classical oracle planner is complete -/

/-- Oracle that decides solvability by classical choice. -/
noncomputable def oracle {C : Type*} [TopologicalSpace C] : Planner C :=
  fun P _ => if h : PathProblem.Solvable C P then
    PlannerAnswer.found (Classical.choose h)
  else PlannerAnswer.noPath

theorem oracle_sound {C : Type*} [TopologicalSpace C] :
    (oracle : Planner C).Sound := by
  constructor
  · intro P k γ hEq
    simp only [oracle] at hEq
    by_cases hSolv : PathProblem.Solvable C P
    · rw [dite_eq_left hSolv] at hEq
      cases hEq
      exact Classical.choose_spec hSolv
    · rw [dite_eq_right hSolv] at hEq
      cases hEq
  · intro P k hEq
    simp only [oracle] at hEq
    by_cases hSolv : PathProblem.Solvable C P
    · rw [dite_eq_left hSolv] at hEq
      cases hEq
    · rw [dite_eq_right hSolv] at hEq
      cases hEq
      exact hSolv

theorem oracle_complete {C : Type*} [TopologicalSpace C] :
    (oracle : Planner C).Complete := by
  refine ⟨oracle_sound, fun P => ?_⟩
  refine ⟨0, ?_⟩
  simp only [oracle]
  by_cases hSolv : PathProblem.Solvable C P
  · rw [dite_eq_left hSolv]
    simp
  · rw [dite_eq_right hSolv]
    simp

/-- Sanity check: completeness implies resolution completeness on the oracle. -/
theorem oracle_resolutionComplete {C : Type*} [TopologicalSpace C] :
    (oracle : Planner C).ResolutionComplete :=
  oracle_complete.resolutionComplete

/-! ## Test 4: probabilistic completeness -/

/-- Robust feasibility implies solvability. -/
theorem solvable_of_robustlyFeasible {C : Type*} [MetricSpace C]
    {P : PathProblem C} (h : P.RobustlyFeasible) :
    PathProblem.Solvable C P := by
  obtain ⟨γ, δ, -, hSol, -⟩ := h
  exact ⟨γ, hSol⟩

/-- A concrete robustly feasible problem: trivial goal in `ℝ`, everything free. -/
def robustProblem : PathProblem ℝ where
  free := Set.univ
  qI := 0
  qG := 0
  qI_mem := Set.mem_univ 0
  qG_mem := Set.mem_univ 0

theorem robustProblem_robustlyFeasible : robustProblem.RobustlyFeasible := by
  refine ⟨Path.refl 0, 1, one_pos, fun _ => Set.mem_univ _, Set.subset_univ _⟩

/-- A deterministic planner viewed as a random planner (ignoring the sample). -/
def asRandom {C Omega : Type*} [TopologicalSpace C] (A : Planner C) :
    RandomPlanner C Omega :=
  fun P _ k => A P k

theorem oracle_asRandom_probabilisticallyComplete :
    (asRandom (Omega := PUnit) (oracle (C := ℝ))).ProbabilisticallyComplete
      (MeasureTheory.Measure.dirac PUnit.unit) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro P ω k γ hEq
      simp only [asRandom] at hEq
      exact (oracle_sound (C := ℝ)).1 P k γ hEq
    · intro P ω k hEq
      simp only [asRandom] at hEq
      exact (oracle_sound (C := ℝ)).2 P k hEq
  · intro P hRob
    have hSolv : PathProblem.Solvable ℝ P := solvable_of_robustlyFeasible hRob
    have hAll : ∀ N : Nat, ∀ ω : PUnit, ∃ k : Nat, k ≤ N ∧
        ∃ γ : Path P.qI P.qG,
          asRandom (Omega := PUnit) (oracle (C := ℝ)) P ω k =
            PlannerAnswer.found γ := by
      intro N ω
      refine ⟨0, Nat.zero_le N, Classical.choose hSolv, ?_⟩
      simp [asRandom, oracle, dite_eq_left hSolv]
    have hSet : ∀ N : Nat, {ω : PUnit | ∃ k : Nat, k ≤ N ∧
        ∃ γ : Path P.qI P.qG,
          asRandom (Omega := PUnit) (oracle (C := ℝ)) P ω k =
            PlannerAnswer.found γ} = Set.univ :=
      fun N => Set.eq_univ_of_forall (hAll N)
    have h1 : ∀ N : Nat, MeasureTheory.Measure.dirac PUnit.unit {ω : PUnit |
        ∃ k : Nat, k ≤ N ∧ ∃ γ : Path P.qI P.qG,
          asRandom (Omega := PUnit) (oracle (C := ℝ)) P ω k =
            PlannerAnswer.found γ} = 1 := by
      intro N
      rw [hSet N, MeasureTheory.IsProbabilityMeasure.measure_univ]
    exact tendsto_const_nhds.congr (fun N => (h1 N).symm)
  · intro P N
    exact Subsingleton.measurableSet

/-- The random planner that never answers. -/
def alwaysRunningRandom {C Omega : Type*} [TopologicalSpace C] :
    RandomPlanner C Omega :=
  fun _ _ _ => PlannerAnswer.running

theorem alwaysRunningRandom_notPC :
    ¬ (alwaysRunningRandom (C := ℝ) (Omega := PUnit)).ProbabilisticallyComplete
      (MeasureTheory.Measure.dirac PUnit.unit) := by
  rintro ⟨-, hT, -⟩
  have hLim := hT robustProblem robustProblem_robustlyFeasible
  have hEmpty : ∀ N : Nat, {ω : PUnit | ∃ k : Nat, k ≤ N ∧
      ∃ γ : Path robustProblem.qI robustProblem.qG,
        alwaysRunningRandom robustProblem ω k = PlannerAnswer.found γ} = ∅ := by
    intro N
    simp [alwaysRunningRandom]
  have h1 : ∀ N : Nat, MeasureTheory.Measure.dirac PUnit.unit {ω : PUnit |
      ∃ k : Nat, k ≤ N ∧ ∃ γ : Path robustProblem.qI robustProblem.qG,
        alwaysRunningRandom robustProblem ω k = PlannerAnswer.found γ} = 0 := by
    intro N
    rw [hEmpty N, MeasureTheory.measure_empty]
  have hU := tendsto_nhds_unique (hLim.congr h1) tendsto_const_nhds
  exact one_ne_zero hU

/-! ## Test 4 (regression): success events must be measurable -/

/-- Two-point sample space with the trivial sigma-algebra. -/
inductive TwoPoint | pt0 | pt1 deriving DecidableEq

instance : MeasurableSpace TwoPoint := ⊥

/-- Sound planner that finds only at `pt1`. -/
noncomputable def findsOnlyAtPt1 : RandomPlanner ℝ TwoPoint :=
  fun P ω _ => match ω with
    | .pt1 => if h : PathProblem.Solvable ℝ P then PlannerAnswer.found (Classical.choose h) else PlannerAnswer.running
    | .pt0 => PlannerAnswer.running

theorem findsOnlyAtPt1_sound :
    (∀ (P : PathProblem ℝ) (ω : TwoPoint) (k : Nat) (γ : Path P.qI P.qG),
      findsOnlyAtPt1 P ω k = PlannerAnswer.found γ → PathProblem.IsSolution ℝ P γ)
    ∧ ∀ (P : PathProblem ℝ) (ω : TwoPoint) (k : Nat),
      findsOnlyAtPt1 P ω k = PlannerAnswer.noPath → ¬ PathProblem.Solvable ℝ P := by
  constructor
  · intro P ω k γ hEq
    cases ω
    · simp [findsOnlyAtPt1] at hEq
    · simp only [findsOnlyAtPt1] at hEq
      by_cases hSolv : PathProblem.Solvable ℝ P
      · simp [hSolv] at hEq
        cases hEq
        exact Classical.choose_spec hSolv
      · simp [hSolv] at hEq
  · intro P ω k hEq
    cases ω
    · simp [findsOnlyAtPt1] at hEq
    · simp only [findsOnlyAtPt1] at hEq
      by_cases hSolv : PathProblem.Solvable ℝ P
      · simp [hSolv] at hEq
      · simp [hSolv] at hEq

/-- A sound planner whose success singleton is non-measurable is not probabilistically complete. -/
theorem findsOnlyAtPt1_notPC :
    ¬ findsOnlyAtPt1.ProbabilisticallyComplete (MeasureTheory.Measure.dirac TwoPoint.pt0) := by
  rintro ⟨-, -, hMeas⟩
  have hSolv : PathProblem.Solvable ℝ robustProblem :=
    solvable_of_robustlyFeasible robustProblem_robustlyFeasible
  have hM := hMeas robustProblem 0
  have hSet : {ω : TwoPoint | ∃ k : Nat, k ≤ 0 ∧ ∃ γ : Path robustProblem.qI robustProblem.qG,
      findsOnlyAtPt1 robustProblem ω k = PlannerAnswer.found γ} = {TwoPoint.pt1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, γ, hEq⟩
      cases ω
      · simp [findsOnlyAtPt1] at hEq
      · rfl
    · intro hEq
      subst hEq
      refine ⟨0, Nat.le_refl 0, Classical.choose hSolv, ?_⟩
      simp [findsOnlyAtPt1, hSolv]
  rw [hSet] at hM
  have hNot : ¬ MeasurableSet ({TwoPoint.pt1} : Set TwoPoint) := by
    show ¬ @MeasurableSet TwoPoint ⊥ _
    rw [MeasurableSpace.measurableSet_bot_iff]
    rintro (h | h)
    · have hMem : TwoPoint.pt1 ∈ ({TwoPoint.pt1} : Set TwoPoint) := by simp
      rw [h] at hMem
      exact Set.notMem_empty _ hMem
    · have hMem : TwoPoint.pt0 ∈ (Set.univ : Set TwoPoint) := Set.mem_univ _
      rw [← h] at hMem
      simp at hMem
  exact hNot hM

/-! ## Test 5: axioms -/

#print axioms Cslib.Planning.MotionPlanning.Planner.Complete.resolutionComplete

end CSLibExtTest.Planning.MotionPlanning
