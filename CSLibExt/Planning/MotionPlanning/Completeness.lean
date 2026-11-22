/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.ConfigurationSpace
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Planner completeness notions

Step-indexed formalization of the classical completeness notions for motion
planning algorithms: completeness, resolution completeness, and probabilistic
completeness.

A step-indexed planner answers `found`, `noPath`, or `running` at each step
`k : Nat`. "In finite time" means "at some step `k`"; "may run forever" means
"answers `running` at every step".

## References

* LaValle, Planning Algorithms, Ch. 4-5 (notions of completeness).
* MIT 16.410 Lecture 15 (probabilistic completeness, robust feasibility).
-/

@[expose] public section

namespace Cslib.Planning.MotionPlanning


/-!
## New declarations: completeness notions

The predicates below use the step-indexed model: a planner answers at each
step `k : Nat`, and "finite time" is rendered as "there exists a step `k`".
-/

/-- A planner answer at one step: a found path, a no-path report, or still running. -/
inductive PlannerAnswer {C : Type*} [TopologicalSpace C] (P : PathProblem C) where
  | found (gamma : Path P.qI P.qG)
  | noPath
  | running

/-- A step-indexed deterministic planner. -/
def Planner (C : Type*) [TopologicalSpace C] : Type _ :=
  (P : PathProblem C) -> Nat -> PlannerAnswer P

/-- A planner is sound when every found answer is a solution and noPath only on unsolvable problems.

Clause 1 is LaValle, Planning Algorithms, Ch. 4.3.1 Formulation 4.1 (a reported
path must lie in the free set); clause 2 is LaValle, Planning Algorithms, Ch. 5
introduction (a no-path report is correct only when no solution exists). -/
def Planner.Sound {C : Type*} [TopologicalSpace C] (A : Planner C) : Prop :=
  (∀ (P : PathProblem C) (k : Nat) (γ : Path P.qI P.qG),
    A P k = PlannerAnswer.found γ → PathProblem.IsSolution C P γ)
  ∧ ∀ (P : PathProblem C) (k : Nat),
    A P k = PlannerAnswer.noPath → ¬ PathProblem.Solvable C P

/-- Complete (LaValle, Planning Algorithms, Ch. 4.3.1 Formulation 4.1 and Ch. 5
introduction): sound, and on every problem some step gives a non-running answer.

Soundness carries correctness (Ch. 5 introduction "correctly reports", Ch. 4.3.1
Formulation 4.1 "compute a path or correctly report none"); the termination clause
renders Ch. 5 introduction "in a finite amount of time" as existence of a deciding
step `k`. -/
def Planner.Complete {C : Type*} [TopologicalSpace C] (A : Planner C) : Prop :=
  A.Sound ∧ ∀ P : PathProblem C, ∃ k : Nat, A P k ≠ PlannerAnswer.running

/-- Resolution complete (LaValle, Planning Algorithms, Ch. 5 introduction): sound,
and on every solvable problem some step finds a path.

The termination clause renders Ch. 5 introduction "if a solution exists, the
algorithm will find it in finite time" as existence of a finding step `k`; on
unsolvable problems the planner may answer `running` at every step (Ch. 5
introduction "may run forever"). This is the exists-`k` reading, not an
eventually-always reading. -/
def Planner.ResolutionComplete {C : Type*} [TopologicalSpace C] (A : Planner C) : Prop :=
  A.Sound ∧ ∀ P : PathProblem C, PathProblem.Solvable C P →
    ∃ k : Nat, ∃ γ : Path P.qI P.qG, A P k = PlannerAnswer.found γ

theorem Planner.Complete.resolutionComplete {C : Type*} [TopologicalSpace C]
    {A : Planner C} (hA : A.Complete) : A.ResolutionComplete := by
  obtain ⟨hSound, hTerm⟩ := hA
  refine ⟨hSound, fun P hSolv => ?_⟩
  obtain ⟨k, hk⟩ := hTerm P
  cases e : A P k
  · rename_i γ
    exact ⟨k, γ, e⟩
  · exact (hSound.2 P k e hSolv).elim
  · exact (hk e).elim

/-- A step-indexed randomized planner over sample space `Omega`. -/
def RandomPlanner (C : Type*) [TopologicalSpace C] (Omega : Type*) : Type _ :=
  (P : PathProblem C) -> Omega -> Nat -> PlannerAnswer P

/-- Robust feasibility (MIT 16.410): a solution whose delta-thickening stays free.

The witness `γ` is a solution (as in LaValle, Planning Algorithms, Ch. 4.3.1
Formulation 4.1), and for some radius `δ > 0` the `δ`-thickening of its range stays
inside the free set, i.e. the solution survives dilating the obstacles by `δ` (MIT
"robust solution"). -/
def PathProblem.RobustlyFeasible {C : Type*} [MetricSpace C] (P : PathProblem C) : Prop :=
  ∃ γ : Path P.qI P.qG, ∃ δ : ℝ, 0 < δ ∧ PathProblem.IsSolution C P γ ∧
    Metric.thickening δ (Set.range γ) ⊆ P.free

/-- Probabilistically complete (LaValle, Planning Algorithms, Ch. 5 introduction;
MIT 16.410): sound, and on robustly feasible problems the probability of a found
answer by step N tends to 1.

The soundness clauses are the randomized analogues of `Planner.Sound`
(LaValle, Planning Algorithms, Ch. 4.3.1 Formulation 4.1 and Ch. 5 introduction).
The limit clause renders LaValle, Planning Algorithms, Ch. 5 introduction ("with
enough points, the probability that it finds an existing solution converges to one")
and MIT 16.410 (`lim Pr(ALG returns a solution) = 1` on robustly feasible
problems): the probability of having found by step `N` tends to `1`. -/
def RandomPlanner.ProbabilisticallyComplete {C Omega : Type*} [MetricSpace C]
    [MeasurableSpace Omega] (μ : MeasureTheory.Measure Omega) [MeasureTheory.IsProbabilityMeasure μ]
    (A : RandomPlanner C Omega) : Prop :=
  ((∀ (P : PathProblem C) (ω : Omega) (k : Nat) (γ : Path P.qI P.qG),
      A P ω k = PlannerAnswer.found γ → PathProblem.IsSolution C P γ)
    ∧ ∀ (P : PathProblem C) (ω : Omega) (k : Nat),
      A P ω k = PlannerAnswer.noPath → ¬ PathProblem.Solvable C P)
  ∧ (∀ P : PathProblem C, P.RobustlyFeasible →
      Filter.Tendsto (fun N : Nat => μ {ω : Omega | ∃ k : Nat, k ≤ N ∧
        ∃ γ : Path P.qI P.qG, A P ω k = PlannerAnswer.found γ})
        Filter.atTop (nhds 1))
  ∧ ∀ (P : PathProblem C) (N : Nat),
      MeasurableSet {ω : Omega | ∃ k : Nat, k ≤ N ∧
        ∃ γ : Path P.qI P.qG, A P ω k = PlannerAnswer.found γ}

end Cslib.Planning.MotionPlanning
