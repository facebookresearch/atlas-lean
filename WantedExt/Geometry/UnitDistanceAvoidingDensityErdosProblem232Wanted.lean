/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Density of planar sets avoiding unit distances (Erdős Problem 232)

Erdős Problem 232 (Moser): let `m₁` be the supremum of the upper densities `limsup_{R → ∞} λ(A ∩
B_R) / λ(B_R)` of measurable `A ⊆ ℝ²` with no two points at distance `1`. Estimate `m₁`; in
particular, is `m₁ ≤ 1/4`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Geometry.UnitDistanceAvoidingDensityErdosProblem232Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #232, https://www.erdosproblems.com/232 (status
PROVED). UnsolvedMath record UM-30006784 (`EP-232`), dataset ulamai/UnsolvedMath v1.8.0.

`B_R` is the open ball of radius `R` about the origin and the ratio is taken in `ℝ≥0∞`. Only `m₁ ≤
1/4` is formalized, not the open-ended estimate. This is the upper density of Ambrus, Csiszárik,
Matolcsi, Varga and Zsámboki (§1, balls `B(x, R)` about any fixed center `x`), which their Theorem 1
bounds by `0.2470` for every Lebesgue-measurable planar set avoiding unit distances.
-/

open MeasureTheory

/-- Erdős Problem 232, "is `m₁ ≤ 1/4`?": every Lebesgue-measurable `A ⊆ ℝ²` with no two points at
distance `1` has upper density `limsup_{R → ∞} λ(A ∩ B_R) / λ(B_R)` at most `1/4`. -/
def unitDistanceAvoidingDensityAtMostQuarter : Prop :=
  ∀ A : Set (EuclideanSpace ℝ (Fin 2)), MeasurableSet A → (∀ x ∈ A, ∀ y ∈ A, dist x y ≠ 1) →
    Filter.limsup (fun R : ℝ => volume (A ∩ Metric.ball 0 R) /
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)) Filter.atTop ≤ 1 / 4

/--
Resolved true: Ambrus, Csiszárik, Matolcsi, Varga and Zsámboki proved (Theorem 1) that every
Lebesgue-measurable planar set avoiding unit distances has upper density at most `0.2470 < 1/4`,
Erdős's conjecture; erdosproblems.com/232 lists the problem as proved. Source: T. F. Bloom, Erdős
Problems, Problem #232, https://www.erdosproblems.com/232 (status PROVED); resolution: G. Ambrus, A.
Csiszárik, M. Matolcsi, D. Varga and P. Zsámboki, The density of planar sets avoiding unit
distances, Math. Program. 207 (2024), 303-327, arXiv:2207.14179, Theorem 1: any Lebesgue measurable,
1-avoiding planar set has upper density at most 0.2470 < 1/4, with the upper density limsup_{R → ∞}
λ(A ∩ B(x, R)) / λ(B(x, R)) of §1, https://doi.org/10.1007/s10107-023-02012-9.
-/
public theorem_wanted unitDistanceAvoidingDensityAtMostQuarter_holds :
    unitDistanceAvoidingDensityAtMostQuarter

end MathlibExt.Geometry.UnitDistanceAvoidingDensityErdosProblem232Wanted
