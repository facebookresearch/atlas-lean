/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Order.Filter.ENNReal
public import Mathlib.Algebra.Module.ZLattice.Basic

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.Geometry.SpherePackingDensityFourWanted

/-!
# Sphere-packing density in four dimensions

Source: optimizationproblems `constants/36a.md`, frozen catalogue SHA256
`5be76ae842abb1b5154ab2fd538c4c5c4cebd91ee72b0fc009bd6ba99fd9b89b`;
H. Cohn and N. Elkies, *New upper bounds on sphere packings I*, Annals of
Mathematics 157 (2003), 689--714, arXiv:math/0110009, Appendix A and Table 3;
D. de Laat, F. M. de Oliveira Filho and F. Vallentin, *Upper bounds for packings
of spheres of several radii*, Forum of Mathematics, Sigma 2 (2014),
DOI 10.1017/fms.2014.24, arXiv:1206.2608, Section 1.4 and Table 1.

The observation-center supremum is taken before the radius limsup. The region
is the union of closed congruent balls; disjoint open interiors allow tangency.
Positive observation radii exclude a zero-volume denominator. `ENNReal` is
the complete-lattice measure codomain; the proved bound by one makes the
optimized value finite. No optimum-attainment assertion is made.

The three displayed upper decimals and the displayed lower decimal are
approximations to the exact converted expressions, not extra exact bounds.
The primary tables call their center-density numbers bounds. Their numerical
certificates have not been replayed here. The four deep bound statements and
periodic approximation are `theorem_wanted` goals, not proofs or axioms.
The catalogue states no open exact-value conjecture, so this is a WantedExt
entry, not an OpenConjectures entry.
-/

noncomputable section

/-- Source: CE2003, the ambient Euclidean space `ℝ⁴`. -/
abbrev Space := EuclideanSpace ℝ (Fin 4)

/-- Source: CE2003 Appendix A, positive observation radii tending to infinity. -/
abbrev PositiveRadius := {R : ℝ // 0 < R}

/-- Source: CE2003 introduction, congruent positive-radius balls with disjoint interiors. -/
structure Packing where
  radius : ℝ
  radius_pos : 0 < radius
  centers : Set Space
  interior_disjoint : centers.PairwiseDisjoint (fun c => Metric.ball c radius)

/-- Source: CE2003, the packed closed ball at a center, including its boundary. -/
def packedBall (P : Packing) (c : Space) : Set Space := Metric.closedBall c P.radius

/-- Source: CE2003 Appendix A, the union `P` of all packed balls. -/
def packingRegion (P : Packing) : Set Space := ⋃ c ∈ P.centers, packedBall P c

/-- Source: CE2003 Appendix A, `vol(P ∩ B(p,R)) / vol(B(p,R))`. -/
def finiteRadiusDensity (P : Packing) (p : Space) (R : PositiveRadius) : ENNReal :=
  volume (packingRegion P ∩ Metric.ball p (R : ℝ)) / volume (Metric.ball p (R : ℝ))

/-- Source: CE2003 Appendix A, supremum over all observation centers at fixed radius. -/
def centeredRadiusDensity (P : Packing) (R : PositiveRadius) : ENNReal :=
  ⨆ p : Space, finiteRadiusDensity P p R

/-- Source: CE2003 Appendix A, limsup as positive radii tend to infinity. -/
def upperDensity (P : Packing) : ENNReal :=
  Filter.limsup (centeredRadiusDensity P) Filter.atTop

/-- Source: catalogue C36, supremum over all congruent-ball packings in `ℝ⁴`. -/
def spherePackingDensity4 : ENNReal := ⨆ P : Packing, upperDensity P

/-- Source: dLOV2014 Section 1.4, volume of a unit ball in `ℝ⁴`. -/
def unitBallVolume4 : ENNReal := volume (Metric.ball (0 : Space) 1)

/-- Source: dLOV2014 Section 1.4, `δ₄ = Δ₄ / vol(B)` for unit spheres. -/
def centerDensity4 : ENNReal := spherePackingDensity4 / unitBallVolume4

/-- Source: CE2003 introduction, finite union of translates of a full-rank lattice.
The lattice is the integer span of a real basis, not an arbitrary periodicity oracle. -/
def Packing.IsPeriodic (P : Packing) : Prop :=
  ∃ (b : Module.Basis (Fin 4) ℝ Space) (offsets : Finset Space),
    P.centers = ⋃ c ∈ offsets,
      (fun w : Space => c + w) '' (Submodule.span ℤ (Set.range b) : Set Space)

/-- Source: catalogue C36, trivial upper-bound row. -/
def upperBound_trivial : Prop := spherePackingDensity4 ≤ 1

/-- Source: catalogue C36, trivial nonnegative lower-bound row. -/
def lowerBound_trivial : Prop := 0 ≤ spherePackingDensity4

/-- Source: packing admission conditions;
disjoint nonempty open balls have countably many centers. -/
theorem centers_countable (P : Packing) : P.centers.Countable :=
  P.interior_disjoint.countable_of_isOpen (fun _ _ => Metric.isOpen_ball)
    (fun _ _ => Metric.nonempty_ball.mpr P.radius_pos)

/-- Source: the covered region is Lebesgue measurable, without an extra packing restriction. -/
theorem packingRegion_measurable (P : Packing) : MeasurableSet (packingRegion P) :=
  MeasurableSet.biUnion (centers_countable P) (fun _ _ => measurableSet_closedBall)

/-- Source: positive observation radii give nonzero volume denominators. -/
theorem observationVolume_ne_zero (p : Space) (R : PositiveRadius) :
    volume (Metric.ball p (R : ℝ)) ≠ 0 :=
  ne_of_gt (Metric.measure_ball_pos volume p R.property)

/-- Source: every finite-radius observation ball has finite volume. -/
theorem observationVolume_ne_top (p : Space) (R : PositiveRadius) :
    volume (Metric.ball p (R : ℝ)) ≠ ⊤ := measure_ball_ne_top

/-- Source: a covered-volume fraction cannot exceed one. -/
theorem finiteRadiusDensity_le_one (P : Packing) (p : Space) (R : PositiveRadius) :
    finiteRadiusDensity P p R ≤ 1 := by
  rw [finiteRadiusDensity, ENNReal.div_le_iff (observationVolume_ne_zero p R)
    (observationVolume_ne_top p R), one_mul]
  exact measure_mono Set.inter_subset_right

/-- Source: taking the observation-center supremum preserves the bound by one. -/
theorem centeredRadiusDensity_le_one (P : Packing) (R : PositiveRadius) :
    centeredRadiusDensity P R ≤ 1 :=
  iSup_le (fun p => finiteRadiusDensity_le_one P p R)

/-- Source: taking the radius limsup preserves the bound by one. -/
theorem upperDensity_le_one (P : Packing) : upperDensity P ≤ 1 := by
  exact Filter.limsup_le_of_le (h := Filter.Eventually.of_forall (centeredRadiusDensity_le_one P))

/-- Source: catalogue C36 trivial upper bound, proved for the actual optimized constant. -/
theorem upperBound_trivial_proved : upperBound_trivial := iSup_le upperDensity_le_one

/-- Source: catalogue C36 trivial lower bound, proved in the measure codomain. -/
theorem lowerBound_trivial_proved : lowerBound_trivial := bot_le

/-- Source: the standard four-dimensional unit-ball volume `π²/2`. -/
theorem unitBallVolume4_eq : unitBallVolume4 = ENNReal.ofReal (Real.pi ^ 2 / 2) := by
  rw [unitBallVolume4, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  norm_num

/-- Source: the center-density divisor is nonzero. -/
theorem unitBallVolume4_ne_zero : unitBallVolume4 ≠ 0 :=
  ne_of_gt (Metric.measure_ball_pos volume (0 : Space) (by norm_num))

/-- Source: the center-density divisor is finite. -/
theorem unitBallVolume4_ne_top : unitBallVolume4 ≠ ⊤ := measure_ball_ne_top

/-- Source: exact conversion between a nonnegative center-density upper bound
and its `π²/2`-scaled volume-density bound. -/
theorem centerDensity_upper_iff (a : ℝ) (ha : 0 ≤ a) :
    centerDensity4 ≤ ENNReal.ofReal a ↔
      spherePackingDensity4 ≤ ENNReal.ofReal ((Real.pi ^ 2 / 2) * a) := by
  rw [centerDensity4, ENNReal.div_le_iff unitBallVolume4_ne_zero unitBallVolume4_ne_top,
    unitBallVolume4_eq, ← ENNReal.ofReal_mul ha, mul_comm]


end
end MathlibExt.Geometry.SpherePackingDensityFourWanted
