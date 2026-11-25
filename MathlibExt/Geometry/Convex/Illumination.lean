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

/-- **Illumination by a direction.** Let $K \subseteq \mathbb{R}^n$ be a set and let
$v, x \in \mathbb{R}^n$. The direction $v$ illuminates $x$ with respect to $K$ when $x$ lies on
the boundary of $K$, $\|v\| = 1$, and $x + tv$ lies in the interior of $K$ for some real
$t > 0$. -/
def DirectionIlluminates {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (v x : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ frontier K ∧ ‖v‖ = 1 ∧ ∃ t : ℝ, 0 < t ∧ x + t • v ∈ interior K

/-- **Illumination by $q$ directions.** A set $K \subseteq \mathbb{R}^n$ is illuminated by $q$
directions, for a natural number $q$, if there are unit vectors $v_1, \dots, v_q \in \mathbb{R}^n$
(not necessarily distinct) such that for every boundary point $x$ of $K$ there are an index $i$
and a real $t > 0$ with $x + tv_i$ in the interior of $K$. -/
def IlluminatedByDirections {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) : Prop :=
  ∃ v : Fin q → EuclideanSpace ℝ (Fin n),
    (∀ i, ‖v i‖ = 1) ∧ ∀ x ∈ frontier K, ∃ i, DirectionIlluminates K (v i) x

/-- **Illumination by an external point.** Let $K \subseteq \mathbb{R}^n$ be a set and let
$p, x \in \mathbb{R}^n$. The point $p$ illuminates $x$ with respect to $K$ when $p \notin K$, $x$
lies on the boundary of $K$, and $p + t(x - p)$ lies in the interior of $K$ for some real $t > 1$;
that is, the ray from $p$ through $x$ meets the interior of $K$ at a point beyond $x$. -/
def ExternalPointIlluminates {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (p x : EuclideanSpace ℝ (Fin n)) : Prop :=
  p ∉ K ∧ x ∈ frontier K ∧ ∃ t : ℝ, 1 < t ∧ p + t • (x - p) ∈ interior K

/-- **Illumination by $q$ external points.** A set $K \subseteq \mathbb{R}^n$ is illuminated by $q$
external points, for a natural number $q$, if there are points
$p_1, \dots, p_q \in \mathbb{R}^n \setminus K$ (not necessarily distinct) such that for every
boundary point $x$ of $K$ there are an index $i$ and a real $t > 1$ with $p_i + t(x - p_i)$ in the
interior of $K$. -/
def IlluminatedByExternalPoints {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) : Prop :=
  ∃ p : Fin q → EuclideanSpace ℝ (Fin n),
    (∀ i, p i ∉ K) ∧ ∀ x ∈ frontier K, ∃ i, ExternalPointIlluminates K (p i) x

/-- **Directional illumination number.** The directional illumination number of a set
$K \subseteq \mathbb{R}^n$ is the least natural number $q$ such that $K$ is illuminated by $q$
directions, and $\infty$ if there is no such $q$. -/
noncomputable def directionalIlluminationNumber {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q | IlluminatedByDirections K q})

/-- **External-point illumination number.** The external-point illumination number of a set
$K \subseteq \mathbb{R}^n$ is the least natural number $q$ such that $K$ is illuminated by $q$
external points, and $\infty$ if there is no such $q$. -/
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
