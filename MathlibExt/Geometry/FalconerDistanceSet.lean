/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Euclidean distance sets and the finite planar threshold

Adapted from the canonical FalconerDistanceSet entry and retained C34a catalogue
formalization by `/root/audit_c1a_final`. Source/API repair and new proofs are
local Codex work by `/root/finish_c32_saved`.
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FalconerDistanceSet

/-- **Euclidean distance set.** For a set $E \subseteq \mathbb{R}^d$, the distance set of $E$ is
$\Delta(E) = \{\lvert x - y \rvert : x, y \in E\}$, the set of Euclidean distances between pairs
of points of $E$.

Source: Guth, Iosevich, Ou, and Wang, arXiv:1808.09346v1, introduction. -/
def distanceSet {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

/-- **Planar Falconer threshold property.** An element $s \in [0, \infty]$ has the planar
threshold property when every compact set $E \subseteq \mathbb{R}^2$ with Hausdorff dimension
$\dim_H E > s$ has a distance set $\{|x - y| : x, y \in E\}$ of positive one-dimensional
Lebesgue measure.

Source: the planar Falconer threshold in optimization catalogue C34a. -/
def planarThresholdProperty (s : ℝ≥0∞) : Prop :=
  ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E →
    s < dimH E → 0 < volume (distanceSet E)

/-- **Admissible planar threshold.** An extended nonnegative real $s$ is an admissible planar
threshold when $0 \le s \le 2$ and $s$ has the planar threshold property: every compact set
$E \subseteq \mathbb{R}^2$ with Hausdorff dimension $\dim_H E > s$ has a distance set of
positive one-dimensional Lebesgue measure.

Source: the defining infimum in optimization catalogue C34a. -/
def admissiblePlanarThreshold (s : ℝ≥0∞) : Prop :=
  s ∈ Set.Icc 0 2 ∧ planarThresholdProperty s

/-- **Planar distance threshold.** The planar distance threshold is the infimum, taken in
$[0, \infty]$, of the admissible planar thresholds, that is, of all $s \in [0, 2]$ such that
every compact subset $E$ of the Euclidean plane $\mathbb{R}^2$ with Hausdorff dimension greater
than $s$ has a distance set of positive Lebesgue measure.

Source: optimization catalogue C34a. The finite ENNReal representation retains
the source's order and measure; finiteness and the real roundtrip are proved below. -/
noncomputable def planarDistanceThreshold : ℝ≥0∞ :=
  sInf {s | admissiblePlanarThreshold s}

/-- **Distances are nonnegative.** For every set $E \subseteq \mathbb{R}^d$, the distance set of
$E$ is contained in $[0, \infty)$. -/
theorem distanceSet_subset_nonnegative {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) :
    distanceSet E ⊆ Set.Ici (0 : ℝ) := by
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact dist_nonneg

/-- **Distance set of the empty set.** For every $d$, the distance set of the empty subset of
$\mathbb{R}^d$ is empty. -/
theorem distanceSet_empty (d : ℕ) : distanceSet (∅ : Set (EuclideanSpace ℝ (Fin d))) = ∅ := by
  ext r
  simp [distanceSet]

/-- **Distance set of a singleton.** For every point $x \in \mathbb{R}^d$, the distance set of
$\{x\}$ is $\{0\}$. -/
theorem distanceSet_singleton {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    distanceSet ({x} : Set (EuclideanSpace ℝ (Fin d))) = {0} := by
  ext r
  simp [distanceSet]

/-- **Distance sets of compact sets are compact.** If $E \subseteq \mathbb{R}^d$ is compact,
then the distance set of $E$ is a compact subset of $\mathbb{R}$. -/
theorem distanceSet_isCompact {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsCompact E) : IsCompact (distanceSet E) := by
  have heq : distanceSet E = (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      dist p.1 p.2) '' (E ×ˢ E) := by
    ext r
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨(x, y), ⟨hx, hy⟩, hxy⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, hxy⟩
      exact ⟨x, hx, y, hy, hxy⟩
  rw [heq]
  exact (h.prod h).image continuous_dist

/-- **Distance sets of compact sets are Borel.** If $E \subseteq \mathbb{R}^d$ is compact, then
the distance set of $E$ is a Borel measurable subset of $\mathbb{R}$. -/
theorem distanceSet_measurableSet {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsCompact E) : MeasurableSet (distanceSet E) :=
  (distanceSet_isCompact h).measurableSet

/-- **The planar threshold property is upward closed.** Let $s \le t$ be elements of
$[0, \infty]$. If $s$ has the planar threshold property, that is, every compact set
$E \subseteq \mathbb{R}^2$ with Hausdorff dimension $\dim_H E > s$ has a distance set of
positive one-dimensional Lebesgue measure, then $t$ has the planar threshold property. -/
theorem planarThresholdProperty_mono {s t : ℝ≥0∞} (hs : planarThresholdProperty s)
    (hst : s ≤ t) : planarThresholdProperty t := by
  intro E hcompact hdim
  exact hs E hcompact (lt_of_le_of_lt hst hdim)

/-- **Subsets of the plane have Hausdorff dimension at most two.** Every subset $E$ of the
Euclidean plane $\mathbb{R}^2$ satisfies $\dim_H E \le 2$. -/
theorem dimH_plane_le_two (E : Set (EuclideanSpace ℝ (Fin 2))) : dimH E ≤ (2 : ℝ≥0∞) := by
  calc
    dimH E ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) := dimH_mono (Set.subset_univ E)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank]; simp

/-- **Two is an admissible planar threshold.** The number $2$ is an admissible planar threshold:
$2 \in [0, 2]$, and every compact set $E \subseteq \mathbb{R}^2$ with Hausdorff dimension
$\dim_H E > 2$ has a distance set of positive Lebesgue measure. This holds vacuously, since no
subset of the plane has Hausdorff dimension greater than $2$. -/
theorem two_admissiblePlanarThreshold : admissiblePlanarThreshold 2 := by
  refine ⟨by simp, ?_⟩
  intro E hcompact hdim
  exact False.elim (not_lt_of_ge (dimH_plane_le_two E) hdim)

/-- **Admissible planar thresholds exist.** There is an admissible planar threshold, that is, the
set of admissible planar thresholds is nonempty. -/
theorem admissiblePlanarThresholds_nonempty : {s | admissiblePlanarThreshold s}.Nonempty :=
  ⟨2, two_admissiblePlanarThreshold⟩

/-- **Admissible thresholds bound the planar distance threshold.** For every $s \in [0, \infty]$
that is an admissible planar threshold, the planar distance threshold is at most $s$. -/
theorem planarDistanceThreshold_le_of_admissible {s : ℝ≥0∞}
    (hs : admissiblePlanarThreshold s) : planarDistanceThreshold ≤ s := sInf_le hs

/-- **The planar distance threshold is at most two.** The planar distance threshold is at most
$2$. -/
theorem planarDistanceThreshold_le_two : planarDistanceThreshold ≤ 2 :=
  planarDistanceThreshold_le_of_admissible two_admissiblePlanarThreshold

/-- **The planar distance threshold is finite.** The planar distance threshold, an element of
$[0, \infty]$, is not $\infty$. -/
theorem planarDistanceThreshold_ne_top : planarDistanceThreshold ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt planarDistanceThreshold_le_two (by norm_num))

/-- **Real round trip of the planar distance threshold.** Let $\tau \in [0, \infty]$ be the planar
distance threshold and let $\tau_{\mathbb{R}}$ be its value as a real number (with the convention
that $\infty$ goes to $0$). Viewing $\tau_{\mathbb{R}}$ again as an element of $[0, \infty]$
gives back $\tau$. -/
theorem planarDistanceThreshold_ofReal_toReal :
    ENNReal.ofReal planarDistanceThreshold.toReal = planarDistanceThreshold :=
  ENNReal.ofReal_toReal planarDistanceThreshold_ne_top

/-- **Trivial lower bound for the planar distance threshold.** The planar distance threshold is
at least $0$. -/
theorem trivialLowerBound : (0 : ℝ≥0∞) ≤ planarDistanceThreshold := bot_le

/-- **Thresholds up to two with the planar threshold property bound the planar distance
threshold.** For every $s \in [0, \infty]$ with $s \le 2$ that has the planar threshold
property, the planar distance threshold is at most $s$. -/
theorem planarDistanceThreshold_le_of_property {s : ℝ≥0∞} (hs : s ≤ 2)
    (hproperty : planarThresholdProperty s) : planarDistanceThreshold ≤ s :=
  planarDistanceThreshold_le_of_admissible ⟨⟨bot_le, hs⟩, hproperty⟩

/-- **Zero-measure distance sets give lower bounds for the planar distance threshold.** Let
$t \in [0, \infty]$. If $E$ is a compact subset of the Euclidean plane $\mathbb{R}^2$ whose
Hausdorff dimension $\dim_H E$ satisfies $t \le \dim_H E$ and whose distance set has Lebesgue
measure zero, then $t$ is at most the planar distance threshold. -/
theorem le_planarDistanceThreshold_of_zeroMeasureWitness {t : ℝ≥0∞}
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hcompact : IsCompact E) (hdim : t ≤ dimH E)
    (hzero : volume (distanceSet E) = 0) : t ≤ planarDistanceThreshold := by
  apply le_sInf
  intro s hs
  by_contra h
  have hpos := hs.2 E hcompact (lt_of_lt_of_le (lt_of_not_ge h) hdim)
  simp [hzero] at hpos

/-- **Real form of admissible planar thresholds.** For every real number $s \ge 0$, $s$ is an
admissible planar threshold (as an element of $[0, \infty]$) if and only if $s \in [0, 2]$ and
$s$ has the planar threshold property. -/
theorem ofReal_admissiblePlanarThreshold_iff {s : ℝ} (hs : 0 ≤ s) :
    admissiblePlanarThreshold (ENNReal.ofReal s) ↔
      s ∈ Set.Icc (0 : ℝ) 2 ∧ planarThresholdProperty (ENNReal.ofReal s) := by
  constructor
  · intro h
    refine ⟨⟨hs, ?_⟩, h.2⟩
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : 0 ≤ (2 : ℝ))).mp
    simpa using h.1.2
  · intro h
    refine ⟨⟨bot_le, ?_⟩, h.2⟩
    simpa using (ENNReal.ofReal_le_ofReal h.1.2)

/-- **The planar distance threshold is itself a threshold.** Let $s_0 \in [0, \infty]$ be the
planar distance threshold, the infimum of the admissible planar thresholds. Every compact set
$E \subseteq \mathbb{R}^2$ with Hausdorff dimension $\dim_H E > s_0$ has a distance set of
positive one-dimensional Lebesgue measure. -/
theorem planarThresholdProperty_planarDistanceThreshold :
    planarThresholdProperty planarDistanceThreshold := by
  intro E hcompact hdim
  obtain ⟨s, hs, hsdim⟩ := sInf_lt_iff.mp hdim
  exact hs.2 E hcompact hsdim

/-- **The planar distance threshold is admissible.** The planar distance threshold is an
admissible planar threshold: it lies in $[0, 2]$ and has the planar threshold property. -/
theorem planarDistanceThreshold_admissible : admissiblePlanarThreshold planarDistanceThreshold :=
  ⟨⟨bot_le, planarDistanceThreshold_le_two⟩, planarThresholdProperty_planarDistanceThreshold⟩

/-- **The planar distance threshold is attained.** The planar distance threshold is the least
admissible planar threshold: it is itself an admissible planar threshold, and it is at most every
admissible planar threshold. -/
theorem isLeast_admissiblePlanarThresholds :
    IsLeast {s | admissiblePlanarThreshold s} planarDistanceThreshold :=
  ⟨planarDistanceThreshold_admissible, fun _ hs => planarDistanceThreshold_le_of_admissible hs⟩

/-- **Real form of the admissible threshold family.** The set of real numbers $r \in [0, 2]$
such that $r$, viewed as an element of $[0, \infty]$, has the planar threshold property equals
the image of the set of admissible planar thresholds under the map $[0, \infty] \to \mathbb{R}$
that is the identity on finite values and sends $\infty$ to $0$. -/
theorem realThresholdFamily_eq_toReal_image :
    {r : ℝ | r ∈ Set.Icc 0 2 ∧ planarThresholdProperty (ENNReal.ofReal r)} =
      ENNReal.toReal '' {s | admissiblePlanarThreshold s} := by
  ext r
  constructor
  · intro h
    exact ⟨ENNReal.ofReal r, (ofReal_admissiblePlanarThreshold_iff h.1.1).mpr h,
      ENNReal.toReal_ofReal h.1.1⟩
  · rintro ⟨s, hs, rfl⟩
    have hn : s ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hs.1.2 (by norm_num))
    refine ⟨⟨ENNReal.toReal_nonneg, ?_⟩, ?_⟩
    · have hle := (ENNReal.toReal_le_toReal hn (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr hs.1.2
      simpa using hle
    · simpa [ENNReal.ofReal_toReal hn] using hs.2

/-- **The planar distance threshold as a real infimum.** The value of the planar distance
threshold as a real number (with the convention that $\infty$ goes to $0$) equals the infimum
in $\mathbb{R}$ of the set of real numbers $r \in [0, 2]$ that, as elements of $[0, \infty]$,
have the planar threshold property. -/
theorem planarDistanceThreshold_toReal_eq_real_sInf :
    planarDistanceThreshold.toReal =
      sInf {r : ℝ | r ∈ Set.Icc 0 2 ∧ planarThresholdProperty (ENNReal.ofReal r)} := by
  rw [planarDistanceThreshold, ENNReal.toReal_sInf, ← realThresholdFamily_eq_toReal_image]
  intro s hs
  exact ne_of_lt (lt_of_le_of_lt hs.1.2 (by norm_num))

end FalconerDistanceSet
