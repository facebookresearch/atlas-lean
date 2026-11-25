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

/-- **Statement of Falconer's distance set theorem.** This is the proposition that for every
integer $d \ge 2$ and every compact set $E \subseteq \mathbb{R}^d$ whose Hausdorff dimension is
strictly greater than $(d+1)/2$, the distance set $\{\|x - y\| : x, y \in E\}$ has positive
one-dimensional Lebesgue measure.

Source: GIOW, arXiv:1808.09346v1, introduction line 76, reporting Falconer (1985). -/
def falconer1985GeneralSufficiency : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E →
    ((d : ℝ≥0∞) + 1) / 2 < dimH E → 0 < volume (FalconerDistanceSet.distanceSet E)

/-- **Wolff's planar distance set condition, as a proposition.** The proposition that every
compact set $E \subseteq \mathbb{R}^2$ with Hausdorff dimension greater than $4/3$ has a distance
set $\{|x - y| : x, y \in E\}$ of positive Lebesgue measure.

Source: GIOW, arXiv:1808.09346v1, introduction line 78, reporting Wolff (1999). -/
def wolff1999PlanarSufficiency : Prop :=
  FalconerDistanceSet.planarThresholdProperty ((4 : ℝ≥0∞) / 3)

/-- **Statement of the Guth–Iosevich–Ou–Wang planar distance set theorem.** This is the
proposition that $5/4$ has the planar threshold property: every compact set
$E \subseteq \mathbb{R}^2$ whose Hausdorff dimension is strictly greater than $5/4$ has a
distance set $\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure.

Source: Guth, Iosevich, Ou, and Wang, arXiv:1808.09346v1, Theorem 1.1, lines 80-81. -/
def guthIosevichOuWang2018PlanarSufficiency : Prop :=
  FalconerDistanceSet.planarThresholdProperty ((5 : ℝ≥0∞) / 4)

/-- **Statement of Falconer's measure-zero distance set examples.** This is the proposition
that for every integer $d \ge 2$ and every $s$ with $0 \le s \le d/2$, there is a compact set
$E \subseteq \mathbb{R}^d$ of Hausdorff dimension exactly $s$ whose distance set
$\{\|x - y\| : x, y \in E\}$ has one-dimensional Lebesgue measure zero.

Source: GIOW, arXiv:1808.09346v1, introduction line 76. Dimensions use actual
Hausdorff dimension and distance sets use actual one-dimensional Lebesgue measure. -/
def falconer1985LatticeExamples : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ s : ℝ≥0∞, s ≤ (d : ℝ≥0∞) / 2 →
    ∃ E : Set (EuclideanSpace ℝ (Fin d)), IsCompact E ∧
      dimH E = s ∧ volume (FalconerDistanceSet.distanceSet E) = 0

/-- **Statement of the upper bound $3/2$ for the planar distance threshold.** This is the
proposition that the planar distance threshold, the infimum of all $s \in [0, 2]$ such that
every compact set $E \subseteq \mathbb{R}^2$ of Hausdorff dimension strictly greater than $s$
has a distance set $\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure,
is at most $3/2$.

Source: optimization catalogue C34a, Falconer (1985) upper row. -/
def upperBound_Falconer1985 : Prop :=
  FalconerDistanceSet.planarDistanceThreshold ≤ (3 : ℝ≥0∞) / 2

/-- **The Wolff bound, as a proposition.** The proposition that the planar Falconer distance
threshold is at most $4/3$. Here the planar Falconer distance threshold is the infimum of the
$s \in [0, 2]$ such that every compact set $E \subseteq \mathbb{R}^2$ with Hausdorff dimension
greater than $s$ has a distance set $\{|x - y| : x, y \in E\}$ of positive Lebesgue measure.

Source: optimization catalogue C34a, Wolff (1999) upper row. -/
def upperBound_Wolff1999 : Prop :=
  FalconerDistanceSet.planarDistanceThreshold ≤ (4 : ℝ≥0∞) / 3

/-- **The Guth–Iosevich–Ou–Wang bound, as a proposition.** The proposition that the planar
Falconer distance threshold is at most $5/4$. Here the planar Falconer distance threshold is the
infimum of the $s \in [0, 2]$ such that every compact set $E \subseteq \mathbb{R}^2$ with
Hausdorff dimension greater than $s$ has a distance set $\{|x - y| : x, y \in E\}$ of positive
Lebesgue measure.

Source: optimization catalogue C34a, GIOW (2018) upper row. -/
def upperBound_GIOW2018 : Prop :=
  FalconerDistanceSet.planarDistanceThreshold ≤ (5 : ℝ≥0∞) / 4

/-- **Statement of the lower bound $1$ for the planar distance threshold.** This is the
proposition that the planar distance threshold, the infimum of all $s \in [0, 2]$ such that
every compact set $E \subseteq \mathbb{R}^2$ of Hausdorff dimension strictly greater than $s$
has a distance set $\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure,
is at least $1$.

Source: optimization catalogue C34a and GIOW's endpoint lattice examples, line 76. -/
def lowerBound_Falconer1985 : Prop :=
  (1 : ℝ≥0∞) ≤ FalconerDistanceSet.planarDistanceThreshold

/-- **Falconer's distance set theorem.** For every integer $d \ge 2$ and every compact set
$E \subseteq \mathbb{R}^d$ whose Hausdorff dimension is strictly greater than $(d+1)/2$, the
distance set $\{\|x - y\| : x, y \in E\}$ has positive one-dimensional Lebesgue measure.

Source: GIOW, arXiv:1808.09346v1, line 76, reporting Falconer (1985). -/
theorem_wanted falconer1985GeneralSufficiency_holds : falconer1985GeneralSufficiency

/-- **Wolff's planar distance set theorem.** Every compact set $E \subseteq \mathbb{R}^2$ with
Hausdorff dimension greater than $4/3$ has a distance set $\{|x - y| : x, y \in E\}$ of positive
Lebesgue measure.

Source: GIOW, arXiv:1808.09346v1, line 78, reporting Wolff (1999). -/
theorem_wanted wolff1999PlanarSufficiency_holds : wolff1999PlanarSufficiency

/-- **Guth–Iosevich–Ou–Wang planar distance set theorem.** Every compact set
$E \subseteq \mathbb{R}^2$ whose Hausdorff dimension is strictly greater than $5/4$ has a
distance set $\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure.

Source: GIOW, arXiv:1808.09346v1, Theorem 1.1, lines 80-81. -/
theorem_wanted guthIosevichOuWang2018PlanarSufficiency_holds :
  guthIosevichOuWang2018PlanarSufficiency

/-- **Falconer's measure-zero distance set examples.** For every integer $d \ge 2$ and every
$s$ with $0 \le s \le d/2$, there is a compact set $E \subseteq \mathbb{R}^d$ of Hausdorff
dimension exactly $s$ whose distance set $\{\|x - y\| : x, y \in E\}$ has one-dimensional
Lebesgue measure zero.

Source: GIOW, arXiv:1808.09346v1, endpoint-inclusive lattice report, line 76. -/
theorem_wanted falconer1985LatticeExamples_holds : falconer1985LatticeExamples

/-- **Falconer's upper bound for the planar distance threshold.** The planar distance
threshold, the infimum of all $s \in [0, 2]$ such that every compact set
$E \subseteq \mathbb{R}^2$ of Hausdorff dimension strictly greater than $s$ has a distance set
$\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure, is at most $3/2$.

Source: optimization catalogue C34a, Falconer (1985) upper row. -/
theorem_wanted upperBound_Falconer1985_holds : upperBound_Falconer1985

/-- **Wolff's upper bound for the planar Falconer threshold.** The planar Falconer distance
threshold, the infimum of the $s \in [0, 2]$ such that every compact set
$E \subseteq \mathbb{R}^2$ with Hausdorff dimension greater than $s$ has a distance set
$\{|x - y| : x, y \in E\}$ of positive Lebesgue measure, is at most $4/3$.

Source: optimization catalogue C34a, Wolff (1999) upper row. -/
theorem_wanted upperBound_Wolff1999_holds : upperBound_Wolff1999

/-- **Guth–Iosevich–Ou–Wang upper bound for the planar Falconer threshold.** The planar Falconer
distance threshold, the infimum of the $s \in [0, 2]$ such that every compact set
$E \subseteq \mathbb{R}^2$ with Hausdorff dimension greater than $s$ has a distance set
$\{|x - y| : x, y \in E\}$ of positive Lebesgue measure, is at most $5/4$.

Source: optimization catalogue C34a, GIOW (2018) upper row. -/
theorem_wanted upperBound_GIOW2018_holds : upperBound_GIOW2018

/-- **Falconer's lower bound for the planar distance threshold.** The planar distance
threshold, the infimum of all $s \in [0, 2]$ such that every compact set
$E \subseteq \mathbb{R}^2$ of Hausdorff dimension strictly greater than $s$ has a distance set
$\{\|x - y\| : x, y \in E\}$ of positive one-dimensional Lebesgue measure, is at least $1$.

Source: optimization catalogue C34a and GIOW, arXiv:1808.09346v1, line 76. -/
theorem_wanted lowerBound_Falconer1985_holds : lowerBound_Falconer1985

end FalconerDistanceSetWanted
