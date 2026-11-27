/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.Probability

@[expose] public section

/-! # Uniform-box specialization of the sampling-planner probability lift

This file specializes the generic i.i.d. sample lift for sampling-based motion
planners (`sPRM`, `PRM*`, `RRT`, `RRT*`) to uniform random samples on a box
`B : SourceBox d` in dimension `d ≥ 2`. The sampling model is unchanged: at step
`N` each planner reads the first `N` raw samples of an infinite stream drawn
from the product law on `ℕ → Fin d → ℝ` with marginal `B.law`, then applies its
own collision filter. Each theorem below instantiates the matching generic lift
statement at `ν := B.law`. The box law generalizes the independent uniform
samples on the unit cube of Karaman and Frazzoli (2011, Sections 2.1 and 3.1).
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

namespace SourceBox

/-- Box specialization: sPRM vertices lift under uniform sampling on the box. -/
theorem isSampleLift_sprmVertices {d : ℕ} (B : SourceBox d) [DecidableEq (Fin d → ℝ)]
    {O : Oracles (Fin d → ℝ)} (hO : OraclesMeasurable O) (start : Fin d → ℝ) (N : ℕ) :
    IsSampleLift B.law N (sprmVertices O start) := by
  exact Cslib.Planning.MotionPlanning.SamplingPlanners.isSampleLift_sprmVertices hO B.law
    start N

/-- Box specialization: sPRM edges lift under uniform sampling on the box. -/
theorem isSampleLift_sprmEdges {d : ℕ} (B : SourceBox d) [DecidableEq (Fin d → ℝ)]
    {O : Oracles (Fin d → ℝ)} (hO : OraclesMeasurable O) (start : Fin d → ℝ) (N : ℕ) :
    IsSampleLift B.law N (sprmEdges O start) := by
  exact Cslib.Planning.MotionPlanning.SamplingPlanners.isSampleLift_sprmEdges hO B.law start N

/-- Box specialization: PRM* vertices lift under uniform sampling on the box. -/
theorem isSampleLift_prmStarVertices {d : ℕ} (B : SourceBox d) [DecidableEq (Fin d → ℝ)]
    {O : Oracles (Fin d → ℝ)} (hO : OraclesMeasurable O) (start : Fin d → ℝ) (N : ℕ) :
    IsSampleLift B.law N (prmStarVertices O start) := by
  exact Cslib.Planning.MotionPlanning.SamplingPlanners.isSampleLift_prmStarVertices hO B.law
    start N

/-- Box specialization: PRM* edges lift under uniform sampling on the box. -/
theorem isSampleLift_prmStarEdges {d : ℕ} (B : SourceBox d) [DecidableEq (Fin d → ℝ)]
    {O : Oracles (Fin d → ℝ)} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : Fin d → ℝ) (N : ℕ) : IsSampleLift B.law N (prmStarEdges O radiusOf start) := by
  exact Cslib.Planning.MotionPlanning.SamplingPlanners.isSampleLift_prmStarEdges hO B.law
    radiusOf start N

/-- Box specialization: RRT lifts under uniform sampling on the box. -/
theorem isSampleLift_rrt {d : ℕ} (B : SourceBox d) [DecidableEq (Fin d → ℝ)]
    {O : Oracles (Fin d → ℝ)} (hO : OraclesMeasurable O) (start : Fin d → ℝ) (N : ℕ) :
    IsSampleLift B.law N (rrt O start) := by
  exact Cslib.Planning.MotionPlanning.SamplingPlanners.isSampleLift_rrt hO B.law start N

/-- Box specialization: RRT* lifts under uniform sampling on the box. -/
theorem isSampleLift_rrtStar {d : ℕ} (B : SourceBox d) [DecidableEq (Fin d → ℝ)]
    {O : Oracles (Fin d → ℝ)} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : Fin d → ℝ) (N : ℕ) : IsSampleLift B.law N (rrtStar O radiusOf start) := by
  exact Cslib.Planning.MotionPlanning.SamplingPlanners.isSampleLift_rrtStar hO B.law radiusOf
    start N

end SourceBox

end Cslib.Planning.MotionPlanning.SamplingPlanners
