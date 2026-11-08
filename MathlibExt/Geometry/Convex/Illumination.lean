/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Convex.Covering
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Actual directional and external-point illumination

Sources: Bezdek and Khan, arXiv:1602.06040v2, introduction;
Arman, Kaire and Prymak, arXiv:2510.25968v3, introduction.
-/

@[expose] public section

namespace ConvexCovering

/-- A unit direction illuminates a boundary point along an inward halfline. -/
def DirectionIlluminates {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (v x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ frontier K ∧ ‖v‖ = 1 ∧ ∃ t : ℝ, 0 < t ∧ x + t • v ∈ interior K

/-- Every boundary point is illuminated by one of a finite family of unit directions. -/
def IlluminatedByDirections {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) : Prop :=
  ∃ v : Fin q → EuclideanSpace ℝ (Fin n),
    (∀ i, ‖v i‖ = 1) ∧ ∀ x ∈ frontier K, ∃ i, DirectionIlluminates K (v i) x

/-- A light outside the body enters its interior strictly beyond the boundary point. -/
def ExternalPointIlluminates {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (p x : EuclideanSpace ℝ (Fin n)) : Prop :=
  p ∉ K ∧ x ∈ frontier K ∧ ∃ t : ℝ, 1 < t ∧ p + t • (x - p) ∈ interior K

/-- A finite family of actual exterior light sources illuminates every boundary point. -/
def IlluminatedByExternalPoints {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) : Prop :=
  ∃ p : Fin q → EuclideanSpace ℝ (Fin n),
    (∀ i, p i ∉ K) ∧ ∀ x ∈ frontier K, ∃ i, ExternalPointIlluminates K (p i) x

/-- The least directional count, with infinity if no finite family exists. -/
noncomputable def directionalIlluminationNumber {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q | IlluminatedByDirections K q})

/-- The corresponding minimum number of actual exterior light sources. -/
noncomputable def externalPointIlluminationNumber {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q | IlluminatedByExternalPoints K q})

theorem externalPointIlluminates_iff_inwardRay {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (p x : EuclideanSpace ℝ (Fin n)) :
    ExternalPointIlluminates K p x ↔
      p ∉ K ∧ x ∈ frontier K ∧ ∃ t : ℝ, 0 < t ∧ x + t • (x - p) ∈ interior K := by
  constructor
  · rintro ⟨hp, hx, t, ht, hi⟩
    refine ⟨hp, hx, t - 1, by linarith, ?_⟩
    convert hi using 1; module
  · rintro ⟨hp, hx, t, ht, hi⟩
    refine ⟨hp, hx, t + 1, by linarith, ?_⟩
    convert hi using 1; module

theorem directionIlluminates_iff_nonnegativeRay {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (v x : EuclideanSpace ℝ (Fin n)) :
    DirectionIlluminates K v x ↔
      x ∈ frontier K ∧ ‖v‖ = 1 ∧ ∃ t : ℝ, 0 ≤ t ∧ x + t • v ∈ interior K := by
  constructor
  · rintro ⟨hx, hv, t, ht, hi⟩
    exact ⟨hx, hv, t, le_of_lt ht, hi⟩
  · rintro ⟨hx, hv, t, ht, hi⟩
    refine ⟨hx, hv, t, ?_, hi⟩
    by_contra h
    have hzero : t = 0 := by linarith
    have hxi : x ∈ interior K := by simpa [hzero] using hi
    exact hx.2 hxi

end ConvexCovering
