/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Geodesic metric spaces

A pseudometric space is *geodesic* if any two points `x` and `y` are joined by a geodesic segment:
a map `γ : ℝ → X` with `γ 0 = x`, `γ (d(x, y)) = y` which is an isometry on `[0, d(x, y)]`.
Unlike the local geodesics of `MathlibExt.Topology.MetricSpace.Geodesic`, these segments realise
the distance globally. Geodesic spaces are the setting of Gromov's thin-triangle formulation of
hyperbolicity (*Hyperbolic groups*, 1987, §1.6 and §6.3) and of the Švarc–Milnor lemma.

## Main definitions

* `Metric.IsGeodesicSegment γ x y`: `γ : ℝ → X` is a geodesic segment from `x` to `y`.
* `Metric.IsGeodesicSpace X`: every two points of `X` are joined by a geodesic segment.

## Main results

* `Metric.IsGeodesicSegment.dist_left`, `.dist_right`: the point `γ t` is at distance `t` from
  `x` and `d(x, y) - t` from `y`.
* `Metric.IsGeodesicSpace.exists_dist_eq_dist_eq`: in a geodesic space, for `0 ≤ t ≤ d(x, y)`
  there is a point `z` with `d(x, z) = t` and `d(z, y) = d(x, y) - t`.
* `Metric.isGeodesicSpace_of_normedSpace`: a real normed space is geodesic.
-/

@[expose] public section

namespace Metric

open Set

variable {X : Type*} [PseudoMetricSpace X]

/-- **Geodesic segment.** A map `γ : ℝ → X` is a geodesic segment from `x` to `y` if `γ 0 = x`,
`γ (dist x y) = y` and `dist (γ s) (γ t) = |s - t|` for all `s t ∈ [0, dist x y]`: it is an
isometry from `[0, dist x y]` onto its image (Gromov, *Hyperbolic groups*, 1987, §1.6). -/
def IsGeodesicSegment (γ : ℝ → X) (x y : X) : Prop :=
  γ 0 = x ∧ γ (dist x y) = y ∧
    ∀ s ∈ Icc 0 (dist x y), ∀ t ∈ Icc 0 (dist x y), dist (γ s) (γ t) = |s - t|

/-- **Geodesic metric space.** A pseudometric space `X` is geodesic if any two points `x y : X`
are joined by a geodesic segment (`Metric.IsGeodesicSegment`) (Gromov, *Hyperbolic groups*, 1987,
§1.6). A segment between points at distance `0` is constant, so a pseudometric space with two
distinct points at distance `0` is never geodesic; the notion is meant for metric spaces. -/
def IsGeodesicSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  ∀ x y : X, ∃ γ : ℝ → X, IsGeodesicSegment γ x y

namespace IsGeodesicSegment

variable {γ : ℝ → X} {x y : X} {t : ℝ}

/-- **Distance from the start of a geodesic segment.** If `γ` is a geodesic segment from `x` to `y`
and `0 ≤ t ≤ d(x, y)`, then `d(x, γ t) = t`. -/
theorem dist_left (hγ : IsGeodesicSegment γ x y) (ht₀ : 0 ≤ t) (ht : t ≤ dist x y) :
    dist x (γ t) = t := by
  obtain ⟨h0, -, h⟩ := hγ
  rw [← h0, h 0 ⟨le_rfl, dist_nonneg⟩ t ⟨ht₀, ht⟩, zero_sub, abs_neg, abs_of_nonneg ht₀]

/-- **Distance to the end of a geodesic segment.** If `γ` is a geodesic segment from `x` to `y`
and `0 ≤ t ≤ d(x, y)`, then `d(γ t, y) = d(x, y) - t`. -/
theorem dist_right (hγ : IsGeodesicSegment γ x y) (ht₀ : 0 ≤ t) (ht : t ≤ dist x y) :
    dist (γ t) y = dist x y - t := by
  obtain ⟨-, h1, h⟩ := hγ
  conv_lhs => rw [← h1]
  rw [h t ⟨ht₀, ht⟩ (dist x y) ⟨dist_nonneg, le_rfl⟩, abs_sub_comm, abs_of_nonneg (by linarith)]

end IsGeodesicSegment

/-- **Points along a geodesic segment.** In a geodesic space, for every `t` with
`0 ≤ t ≤ dist x y` there is a point `z` with `dist x z = t` and `dist z y = dist x y - t`. -/
theorem IsGeodesicSpace.exists_dist_eq_dist_eq (hX : IsGeodesicSpace X) (x y : X) {t : ℝ}
    (ht₀ : 0 ≤ t) (ht : t ≤ dist x y) : ∃ z, dist x z = t ∧ dist z y = dist x y - t := by
  obtain ⟨γ, hγ⟩ := hX x y
  exact ⟨γ t, hγ.dist_left ht₀ ht, hγ.dist_right ht₀ ht⟩

/-- **Normed spaces are geodesic.** A real normed space is a geodesic space: the affine segment
`t ↦ x + (t / d(x, y)) (y - x)` is a geodesic segment from `x` to `y`. -/
theorem isGeodesicSpace_of_normedSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsGeodesicSpace E := by
  intro x y
  by_cases hxy : x = y
  · subst hxy
    refine ⟨fun _ => x, rfl, rfl, fun s hs t ht => ?_⟩
    simp only [dist_self, Icc_self, mem_singleton_iff] at hs ht
    simp [hs, ht]
  · have hd : 0 < dist x y := dist_pos.mpr hxy
    refine ⟨fun t => AffineMap.lineMap x y (t / dist x y), by simp, by simp [hd.ne'], ?_⟩
    intro s _ t _
    rw [dist_lineMap_lineMap, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hd,
      div_mul_cancel₀ _ hd.ne']

end Metric
