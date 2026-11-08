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

/-- The Euclidean distances determined by every pair of points of `E`.

Source: Guth, Iosevich, Ou, and Wang, arXiv:1808.09346v1, introduction. -/
def distanceSet {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) : Set ℝ :=
  {r | ∃ x ∈ E, ∃ y ∈ E, dist x y = r}

/-- A planar threshold forces positive one-dimensional Lebesgue distance measure.

Source: the planar Falconer threshold in optimization catalogue C34a. -/
def planarThresholdProperty (s : ℝ≥0∞) : Prop :=
  ∀ E : Set (EuclideanSpace ℝ (Fin 2)), IsCompact E →
    s < dimH E → 0 < volume (distanceSet E)

/-- Sufficient thresholds in the source's closed interval `[0,2]`.

Source: the defining infimum in optimization catalogue C34a. -/
def admissiblePlanarThreshold (s : ℝ≥0∞) : Prop :=
  s ∈ Set.Icc 0 2 ∧ planarThresholdProperty s

/-- The infimum of sufficient planar thresholds in `[0,2]`.

Source: optimization catalogue C34a. The finite ENNReal representation retains
the source's order and measure; finiteness and the real roundtrip are proved below. -/
noncomputable def planarDistanceThreshold : ℝ≥0∞ :=
  sInf {s | admissiblePlanarThreshold s}

/-- Every realized Euclidean distance is nonnegative. -/
theorem distanceSet_subset_nonnegative {d : ℕ} (E : Set (EuclideanSpace ℝ (Fin d))) :
    distanceSet E ⊆ Set.Ici (0 : ℝ) := by
  rintro r ⟨x, hx, y, hy, rfl⟩
  exact dist_nonneg

/-- The empty set determines no distances. -/
theorem distanceSet_empty (d : ℕ) : distanceSet (∅ : Set (EuclideanSpace ℝ (Fin d))) = ∅ := by
  ext r
  simp [distanceSet]

/-- A singleton determines exactly the distance zero. -/
theorem distanceSet_singleton {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    distanceSet ({x} : Set (EuclideanSpace ℝ (Fin d))) = {0} := by
  ext r
  simp [distanceSet]

/-- Distances of a compact Euclidean set form a compact real set. -/
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

/-- A compact Euclidean distance set is Lebesgue measurable. -/
theorem distanceSet_measurableSet {d : ℕ} {E : Set (EuclideanSpace ℝ (Fin d))}
    (h : IsCompact E) : MeasurableSet (distanceSet E) :=
  (distanceSet_isCompact h).measurableSet

/-- Raising a sufficient strict dimension threshold preserves sufficiency. -/
theorem planarThresholdProperty_mono {s t : ℝ≥0∞} (hs : planarThresholdProperty s)
    (hst : s ≤ t) : planarThresholdProperty t := by
  intro E hcompact hdim
  exact hs E hcompact (lt_of_le_of_lt hst hdim)

/-- Hausdorff dimension of every subset of the Euclidean plane is at most two. -/
theorem dimH_plane_le_two (E : Set (EuclideanSpace ℝ (Fin 2))) : dimH E ≤ (2 : ℝ≥0∞) := by
  calc
    dimH E ≤ dimH (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) := dimH_mono (Set.subset_univ E)
    _ = 2 := by rw [Real.dimH_univ_eq_finrank]; simp

/-- Two is an admissible threshold because no planar set has dimension strictly above two. -/
theorem two_admissiblePlanarThreshold : admissiblePlanarThreshold 2 := by
  refine ⟨by simp, ?_⟩
  intro E hcompact hdim
  exact False.elim (not_lt_of_ge (dimH_plane_le_two E) hdim)

/-- The interval-restricted sufficient-threshold family is nonempty. -/
theorem admissiblePlanarThresholds_nonempty : {s | admissiblePlanarThreshold s}.Nonempty :=
  ⟨2, two_admissiblePlanarThreshold⟩

/-- Every admissible threshold is an upper bound for the defining infimum. -/
theorem planarDistanceThreshold_le_of_admissible {s : ℝ≥0∞}
    (hs : admissiblePlanarThreshold s) : planarDistanceThreshold ≤ s := sInf_le hs

/-- The planar distance threshold is at most two. -/
theorem planarDistanceThreshold_le_two : planarDistanceThreshold ≤ 2 :=
  planarDistanceThreshold_le_of_admissible two_admissiblePlanarThreshold

/-- The planar distance threshold is finite, without any analytic bound being assumed. -/
theorem planarDistanceThreshold_ne_top : planarDistanceThreshold ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt planarDistanceThreshold_le_two (by norm_num))

/-- Conversion to the nonnegative real value and back retains the actual infimum. -/
theorem planarDistanceThreshold_ofReal_toReal :
    ENNReal.ofReal planarDistanceThreshold.toReal = planarDistanceThreshold :=
  ENNReal.ofReal_toReal planarDistanceThreshold_ne_top

/-- The trivial lower bound uses the bottom of the actual nonnegative threshold domain. -/
theorem trivialLowerBound : (0 : ℝ≥0∞) ≤ planarDistanceThreshold := bot_le

/-- A sufficient threshold in the interval gives an upper bound for the infimum. -/
theorem planarDistanceThreshold_le_of_property {s : ℝ≥0∞} (hs : s ≤ 2)
    (hproperty : planarThresholdProperty s) : planarDistanceThreshold ≤ s :=
  planarDistanceThreshold_le_of_admissible ⟨⟨bot_le, hs⟩, hproperty⟩

/-- A compact zero-measure distance example rules out all strictly smaller thresholds. -/
theorem le_planarDistanceThreshold_of_zeroMeasureWitness {t : ℝ≥0∞}
    {E : Set (EuclideanSpace ℝ (Fin 2))} (hcompact : IsCompact E) (hdim : t ≤ dimH E)
    (hzero : volume (distanceSet E) = 0) : t ≤ planarDistanceThreshold := by
  apply le_sInf
  intro s hs
  by_contra h
  have hpos := hs.2 E hcompact (lt_of_lt_of_le (lt_of_not_ge h) hdim)
  simp [hzero] at hpos

/-- Nonnegative real thresholds have exactly the source's real interval domain. -/
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

/-- Strict dimension hypotheses make the infimum itself a sufficient threshold. -/
theorem planarThresholdProperty_planarDistanceThreshold :
    planarThresholdProperty planarDistanceThreshold := by
  intro E hcompact hdim
  obtain ⟨s, hs, hsdim⟩ := sInf_lt_iff.mp hdim
  exact hs.2 E hcompact hsdim

/-- The actual finite infimum belongs to the closed threshold family. -/
theorem planarDistanceThreshold_admissible : admissiblePlanarThreshold planarDistanceThreshold :=
  ⟨⟨bot_le, planarDistanceThreshold_le_two⟩, planarThresholdProperty_planarDistanceThreshold⟩

/-- The infimum is the least sufficient threshold in the source domain. -/
theorem isLeast_admissiblePlanarThresholds :
    IsLeast {s | admissiblePlanarThreshold s} planarDistanceThreshold :=
  ⟨planarDistanceThreshold_admissible, fun _ hs => planarDistanceThreshold_le_of_admissible hs⟩

/-- The real source domain is exactly the image of the finite ENNReal threshold family. -/
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

/-- The finite ENNReal representation gives the exact defining infimum over real `[0,2]`. -/
theorem planarDistanceThreshold_toReal_eq_real_sInf :
    planarDistanceThreshold.toReal =
      sInf {r : ℝ | r ∈ Set.Icc 0 2 ∧ planarThresholdProperty (ENNReal.ofReal r)} := by
  rw [planarDistanceThreshold, ENNReal.toReal_sInf, ← realThresholdFamily_eq_toReal_image]
  intro s hs
  exact ne_of_lt (lt_of_le_of_lt hs.1.2 (by norm_num))

end FalconerDistanceSet
