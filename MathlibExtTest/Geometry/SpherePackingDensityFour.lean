/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.SpherePackingDensityFour

/-!
# Sphere-packing density in dimension four: public API checks

Characterization examples adapted from the retained Codex boundary suite for
`constants/36a.md`. The empty and singleton packings, touching and overlapping
balls, positive observation radii, and density normalization are checked here.
-/

@[expose] public section

namespace MathlibExtTest.Geometry.SpherePackingDensityFour

open Filter MeasureTheory
open MathlibExt.Geometry.SpherePackingDensityFourWanted

noncomputable section

private def emptyPacking : Packing where
  radius := 1
  radius_pos := by norm_num
  centers := ∅
  interior_disjoint := by simp

private def singletonPacking : Packing where
  radius := 1
  radius_pos := by norm_num
  centers := {(0 : Space)}
  interior_disjoint := by simp [Set.PairwiseDisjoint]

private def unitObservationRadius : PositiveRadius := ⟨1, by norm_num⟩

example : ¬ (0 < (0 : ℝ)) := by norm_num
example : ¬ (0 < (-1 : ℝ)) := by norm_num
example : ¬ ∃ R : PositiveRadius, (R : ℝ) = 0 := by
  rintro ⟨R, hR⟩
  simpa [hR] using R.property
example : volume (Metric.ball (0 : Space) 0) = 0 := by simp
example : (unitObservationRadius : ℝ) = 1 := rfl
example (R : PositiveRadius) : ∃ S : PositiveRadius, R < S := by
  refine ⟨⟨(R : ℝ) + 1, by linarith [R.property]⟩, ?_⟩
  change (R : ℝ) < (R : ℝ) + 1
  linarith
example (R : PositiveRadius) : ∃ S : PositiveRadius, S < R := by
  refine ⟨⟨(R : ℝ) / 2, by linarith [R.property]⟩, ?_⟩
  change (R : ℝ) / 2 < (R : ℝ)
  linarith [R.property]

example {x y : Space} (hxy : dist x y = 2) :
    Disjoint (Metric.ball x 1) (Metric.ball y 1) := by
  apply Metric.ball_disjoint_ball
  norm_num
  linarith
example {x y : Space} (hxy : dist x y < 2) :
    ¬ Disjoint (Metric.ball x 1) (Metric.ball y 1) := by
  rw [Set.not_disjoint_iff]
  refine ⟨midpoint ℝ x y, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_midpoint_left]
    norm_num
    linarith
  · rw [Metric.mem_ball, dist_midpoint_right]
    norm_num
    linarith

example (P : Packing) : 0 < P.radius := P.radius_pos
example (P : Packing) :
    P.centers.PairwiseDisjoint (fun c => Metric.ball c P.radius) := P.interior_disjoint
example (P : Packing) : P.centers.Countable := centers_countable P
example (P : Packing) : MeasurableSet (packingRegion P) := packingRegion_measurable P
example (p : Space) (R : PositiveRadius) : volume (Metric.ball p (R : ℝ)) ≠ 0 :=
  observationVolume_ne_zero p R
example (p : Space) (R : PositiveRadius) : volume (Metric.ball p (R : ℝ)) ≠ ⊤ :=
  observationVolume_ne_top p R
example : unitBallVolume4 = ENNReal.ofReal (Real.pi ^ 2 / 2) := unitBallVolume4_eq
example : unitBallVolume4 ≠ 0 := unitBallVolume4_ne_zero
example : unitBallVolume4 ≠ ⊤ := unitBallVolume4_ne_top
example : upperBound_trivial := upperBound_trivial_proved
example : lowerBound_trivial := lowerBound_trivial_proved
example : packingRegion emptyPacking = ∅ := by simp [packingRegion, emptyPacking]
example (p : Space) (R : PositiveRadius) : finiteRadiusDensity emptyPacking p R = 0 := by
  simp [finiteRadiusDensity, packingRegion, emptyPacking]
example : packingRegion singletonPacking = Metric.closedBall (0 : Space) 1 := by
  simp [packingRegion, packedBall, singletonPacking]
example (P : Packing) : spherePackingDensity4 ≥ upperDensity P := le_iSup upperDensity P
example (P : Packing) (R : PositiveRadius) (p : Space) :
    finiteRadiusDensity P p R ≤ centeredRadiusDensity P R :=
  le_iSup (finiteRadiusDensity P · R) p
example : upperDensity = fun P => Filter.limsup (fun (R : PositiveRadius) => ⨆ p : Space,
    volume (packingRegion P ∩ Metric.ball p (R : ℝ)) / volume (Metric.ball p (R : ℝ))) atTop := rfl
example (b : Module.Basis (Fin 4) ℝ Space) : emptyPacking.IsPeriodic := by
  refine ⟨b, ∅, ?_⟩
  simp [emptyPacking]
example (a : ℝ) (ha : 0 ≤ a) :
    centerDensity4 ≤ ENNReal.ofReal a ↔
      spherePackingDensity4 ≤ ENNReal.ofReal ((Real.pi ^ 2 / 2) * a) :=
  centerDensity_upper_iff a ha

example : (atTop : Filter PositiveRadius).NeBot := by
  let : Nonempty PositiveRadius := ⟨unitObservationRadius⟩
  infer_instance

end

end MathlibExtTest.Geometry.SpherePackingDensityFour
