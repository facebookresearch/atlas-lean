/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Planning.MotionPlanning.SamplingPlanners.UniformBox

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-! # Tests for the sampling-planner probability lift

Concrete checks for the generic lift and its uniform-box specialization: raw
prefixes and collision filtering evaluated by `decide`, a measurable oracle on
the unit square, and the box-law unfolding.
-/

/-- Concrete stream on `Int × Int` hitting the test obstacle at `n = 1`. -/
def testStream : ℕ → Int × Int := fun n => ((n : Int), 0)

/-- The raw prefix of the test stream is the expected list of samples. -/
example : rawPrefix 3 testStream = [(0, 0), (1, 0), (2, 0)] := by
  decide

/-- Test oracle on `Int × Int` whose obstacle rejects the sample `(1, 0)`. -/
def testObstacleOracles : Oracles (Int × Int) :=
  { free := fun p => decide (p.1 ≠ 1)
    link := fun _ _ => true
    steer := fun _ s => s
    cost := fun a b => if a = b then 0 else 1
    radius := 1
    cost_nonneg := fun a b => by
      by_cases h : a = b <;> simp [h]
    cost_self := fun a => by simp
    cost_pos := fun _ _ h => by simp [h] }

/-- The obstacle rejects one of the three raw samples. -/
example : freeCount testObstacleOracles 3 testStream < 3 := by
  decide

/-- `rrt` on the raw prefix agrees with `rrt` on the collision-filtered prefix. -/
example : rrt testObstacleOracles (0, 0) (rawPrefix 3 testStream) =
    rrt testObstacleOracles (0, 0)
      ((rawPrefix 3 testStream).filter testObstacleOracles.free) := by
  decide

/-- Test oracle on the unit square, free on the left half and with a real
obstacle on the right half. -/
noncomputable def testSquareOracles : Oracles (Fin 2 → ℝ) := by
  classical
  exact
    { free := fun x => decide (x 0 < 1 / 2)
      link := fun _ _ => true
      steer := fun _ s => s
      cost := fun u v => if u = v then 0 else 1
      radius := 1
      cost_nonneg := fun a b => by
        by_cases h : a = b <;> simp [h]
      cost_self := fun a => by simp
      cost_pos := fun _ _ h => by simp [h] }

/-- The unit-square test oracle is measurable. -/
theorem measurable_testSquareOracles : OraclesMeasurable testSquareOracles := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Measurable (fun x : Fin 2 → ℝ => decide (x 0 < 1 / 2))
    apply measurable_to_bool
    have hpre : (fun x : Fin 2 → ℝ => decide (x 0 < 1 / 2)) ⁻¹' {true}
        = {x | x 0 < 1 / 2} := by
      ext x
      simp
    rw [hpre]
    exact measurableSet_lt (measurable_pi_apply 0) measurable_const
  · show Measurable (fun _ : (Fin 2 → ℝ) × (Fin 2 → ℝ) => true)
    exact measurable_const
  · show Measurable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => p.2)
    exact measurable_snd
  · show Measurable
        (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) => if p.1 = p.2 then (0 : ℚ) else 1)
    have hdiag : MeasurableSet {p : (Fin 2 → ℝ) × (Fin 2 → ℝ) | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    exact Measurable.piecewise hdiag measurable_const measurable_const

/-- The generic RRT* lift applies to the unit-square test oracle. -/
example (radiusOf : ℕ → ℚ) (start : Fin 2 → ℝ) (N : ℕ) :
    IsSampleLift (SourceBox.unitCube 2 le_rfl).law N
      (rrtStar testSquareOracles radiusOf start) := by
  classical
  exact SourceBox.isSampleLift_rrtStar (SourceBox.unitCube 2 le_rfl)
    measurable_testSquareOracles radiusOf start N

/-- The RRT* vertex-event measurability applies to the unit-square test oracle. -/
example (radiusOf : ℕ → ℚ) (start : Fin 2 → ℝ) (N : ℕ) :
    MeasurableSet {ω : ℕ → Fin 2 → ℝ |
      ∃ v ∈ (rrtStar testSquareOracles radiusOf start (rawPrefix N ω)).1,
        v ∈ (Set.univ : Set (Fin 2 → ℝ))} := by
  classical
  exact measurableSet_rrtStar_vertex_event measurable_testSquareOracles radiusOf start N
    MeasurableSet.univ

/-- The box law unfolds to the conditioned volume on the unit square. -/
example (A : Set (Fin 2 → ℝ)) :
    (SourceBox.unitCube 2 le_rfl).law A =
      MeasureTheory.volume (A ∩ (SourceBox.unitCube 2 le_rfl).carrier) /
        MeasureTheory.volume (SourceBox.unitCube 2 le_rfl).carrier :=
  SourceBox.law_apply (SourceBox.unitCube 2 le_rfl) A

end Cslib.Planning.MotionPlanning.SamplingPlanners
