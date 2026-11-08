/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Source requests for the Falconer distance threshold

The implemented Euclidean model and elementary laws are upstream. These eight
source-labelled propositions are private ProofWanted data, not assumed proofs.
Source specifications are adapted from the retained C34a work by
`/root/audit_c1a_final`; the supported split is local Codex work by
`/root/finish_c32_saved`.
-/
module

public import MathlibExt.Geometry.FalconerDistanceSet
public import Batteries.Util.ProofWanted

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FalconerDistanceSetWanted

/-- Falconer's general sufficient exponent is `(d+1)/2`, not `d+1/2`.

Source: GIOW, arXiv:1808.09346v1, introduction line 76, reporting Falconer (1985). -/
def falconer1985GeneralSufficiency : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    ((d : ℝ≥0∞) + 1) / 2 < dimH E → 0 < volume (FalconerDistanceSet.distanceSet E)

/-- Wolff's strict compact planar `4/3` sufficient threshold.

Source: GIOW, arXiv:1808.09346v1, introduction line 78, reporting Wolff (1999). -/
def wolff1999PlanarSufficiency : Prop :=
  FalconerDistanceSet.planarThresholdProperty ((4 : ℝ≥0∞) / 3)

/-- The strict compact planar `5/4` sufficient threshold.

Source: Guth, Iosevich, Ou, and Wang, arXiv:1808.09346v1, Theorem 1.1, lines 80-81. -/
def guthIosevichOuWang2018PlanarSufficiency : Prop :=
  FalconerDistanceSet.planarThresholdProperty ((5 : ℝ≥0∞) / 4)

/-- Compact Euclidean lattice examples include the endpoint `s = d/2`.

Source: GIOW, arXiv:1808.09346v1, introduction line 76. Dimensions use actual
Hausdorff dimension and distance sets use actual one-dimensional Lebesgue measure. -/
def falconer1985LatticeExamples : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ s : ℝ≥0∞, s ≤ (d : ℝ≥0∞) / 2 →
    ∃ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E ∧
      dimH E = s ∧ volume (FalconerDistanceSet.distanceSet E) = 0

/-- The planar threshold is at most `3/2`.

Source: optimization catalogue C34a, Falconer (1985) upper row. -/
def upperBound_Falconer1985 : Prop :=
  FalconerDistanceSet.planarDistanceThreshold ≤ (3 : ℝ≥0∞) / 2

/-- The planar threshold is at most `4/3`.

Source: optimization catalogue C34a, Wolff (1999) upper row. -/
def upperBound_Wolff1999 : Prop :=
  FalconerDistanceSet.planarDistanceThreshold ≤ (4 : ℝ≥0∞) / 3

/-- The planar threshold is at most `5/4`.

Source: optimization catalogue C34a, GIOW (2018) upper row. -/
def upperBound_GIOW2018 : Prop :=
  FalconerDistanceSet.planarDistanceThreshold ≤ (5 : ℝ≥0∞) / 4

/-- The planar threshold is at least one.

Source: optimization catalogue C34a and GIOW's endpoint lattice examples, line 76. -/
def lowerBound_Falconer1985 : Prop :=
  (1 : ℝ≥0∞) ≤ FalconerDistanceSet.planarDistanceThreshold

/-- Source: GIOW, arXiv:1808.09346v1, line 76, reporting Falconer (1985). -/
theorem_wanted falconer1985GeneralSufficiency_holds : falconer1985GeneralSufficiency

/-- Source: GIOW, arXiv:1808.09346v1, line 78, reporting Wolff (1999). -/
theorem_wanted wolff1999PlanarSufficiency_holds : wolff1999PlanarSufficiency

/-- Source: GIOW, arXiv:1808.09346v1, Theorem 1.1, lines 80-81. -/
theorem_wanted guthIosevichOuWang2018PlanarSufficiency_holds :
  guthIosevichOuWang2018PlanarSufficiency

/-- Source: GIOW, arXiv:1808.09346v1, endpoint-inclusive lattice report, line 76. -/
theorem_wanted falconer1985LatticeExamples_holds : falconer1985LatticeExamples

/-- Source: optimization catalogue C34a, Falconer (1985) upper row. -/
theorem_wanted upperBound_Falconer1985_holds : upperBound_Falconer1985

/-- Source: optimization catalogue C34a, Wolff (1999) upper row. -/
theorem_wanted upperBound_Wolff1999_holds : upperBound_Wolff1999

/-- Source: optimization catalogue C34a, GIOW (2018) upper row. -/
theorem_wanted upperBound_GIOW2018_holds : upperBound_GIOW2018

/-- Source: optimization catalogue C34a and GIOW, arXiv:1808.09346v1, line 76. -/
theorem_wanted lowerBound_Falconer1985_holds : lowerBound_Falconer1985

end FalconerDistanceSetWanted
