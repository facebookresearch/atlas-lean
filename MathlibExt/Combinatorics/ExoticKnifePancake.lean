/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Stem–circle intersections of lollipops

If two lollipops have three or four stem–circle intersections, the angle between their stem
directions exceeds $\pi/2$.
-/

namespace MetaMathlibExt

namespace Lollipop

private noncomputable def point (c : ℝ × ℝ) (θ s : ℝ) : ℝ × ℝ :=
  c + s • (Real.cos θ, Real.sin θ)

private def circle (c : ℝ × ℝ) (r : ℝ) : Set (ℝ × ℝ) :=
  {x | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = r ^ 2}

private noncomputable def crossings (c d : ℝ × ℝ) (r R θ : ℝ) : Set (ℝ × ℝ) :=
  point c θ '' Set.Ici r ∩ circle d R

private noncomputable def projection (c d : ℝ × ℝ) (θ : ℝ) : ℝ :=
  (d.1 - c.1) * Real.cos θ + (d.2 - c.2) * Real.sin θ

/-- Two distinct parameters on a chord are symmetric about the projection of the center. -/
private theorem chord_parameters {c d : ℝ × ℝ} {R θ s t : ℝ}
    (hs : point c θ s ∈ circle d R) (ht : point c θ t ∈ circle d R) :
    s = t ∨ s + t = 2 * projection c d θ := by
  have eqn (u : ℝ) (hu : point c θ u ∈ circle d R) :
      (c.1 + u * Real.cos θ - d.1) ^ 2 + (c.2 + u * Real.sin θ - d.2) ^ 2 = R ^ 2 := hu
  have h : (s - t) * (s + t - 2 * projection c d θ) = 0 := by
    unfold projection
    linear_combination eqn s hs - eqn t ht - (s ^ 2 - t ^ 2) * Real.cos_sq_add_sin_sq θ
  simpa only [sub_eq_zero] using mul_eq_zero.mp h

/-- A secant stem meets the circle exactly twice, with its endpoint before the chord midpoint. -/
private theorem secant_crossings {c d : ℝ × ℝ} {r R θ : ℝ}
    (h : 1 < (crossings c d r R θ).ncard) :
    (crossings c d r R θ).ncard = 2 ∧ r < projection c d θ := by
  obtain ⟨_, ⟨⟨s, hs, rfl⟩, hsc⟩, _, ⟨⟨t, ht, rfl⟩, htc⟩, hne⟩ :=
    (Set.one_lt_ncard_iff_nontrivial_and_finite.mp h).1
  have hst : s ≠ t := fun he => hne (congrArg (point c θ) he)
  have hsum := (chord_parameters hsc htc).resolve_left hst
  refine ⟨Set.ncard_eq_two.mpr ⟨_, _, hne, ?_⟩, ?_⟩
  · ext x
    constructor
    · rintro ⟨⟨u, _, rfl⟩, huc⟩
      rcases chord_parameters huc hsc with rfl | hus
      · exact Set.mem_insert _ _
      · have : u = t := by linarith
        simp [this]
    · rintro (rfl | hx)
      · exact ⟨⟨_, hs, rfl⟩, hsc⟩
      · rw [Set.mem_singleton_iff] at hx
        exact hx ▸ ⟨⟨_, ht, rfl⟩, htc⟩
  · change r ≤ s at hs
    change r ≤ t at ht
    rcases lt_or_gt_of_ne hst with hlt | hgt <;> linarith

private theorem projection_le_radius {c x : ℝ × ℝ} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ circle c r) (θ : ℝ) : projection c x θ ≤ r := by
  change (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = r ^ 2 at hx
  apply le_of_mul_le_mul_left (a := 2 * r) _ (by positivity)
  unfold projection
  -- Use the squared distance from x to the point on the circle in direction θ.
  nlinarith only [sq_nonneg (x.1 - c.1 - r * Real.cos θ),
    sq_nonneg (x.2 - c.2 - r * Real.sin θ), hx,
    congrArg (fun z : ℝ => r ^ 2 * z) (Real.cos_sq_add_sin_sq θ)]

private theorem cos_sub_neg_of_secant {c d : ℝ × ℝ} {r R θ φ : ℝ} (hr : 0 < r) (hR : 0 < R)
    (hsec : 1 < (crossings c d r R θ).ncard)
    (htotal : 3 ≤ (crossings c d r R θ).ncard + (crossings d c R r φ).ncard) :
    Real.cos (θ - φ) < 0 := by
  obtain ⟨hcard, hproj⟩ := secant_crossings hsec
  obtain ⟨_, ⟨t, ht, rfl⟩, htc⟩ :=
    Set.nonempty_of_ncard_ne_zero (s := crossings d c R r φ) (by omega)
  have htpos : 0 ≤ t := hR.le.trans ht
  have hbound := projection_le_radius hr htc θ
  have hstep : projection c (point d φ t) θ =
      projection c d θ + t * Real.cos (θ - φ) := by
    simp [projection, point, Real.cos_sub]
    ring
  rw [hstep] at hbound
  by_contra! hcos
  linarith [mul_nonneg htpos hcos]

end Lollipop

open Lollipop

/-- **Stem–circle intersections of two lollipops.** For a point $c = (a, b) \in \mathbb{R}^2$, a
radius $r > 0$ and an angle $\theta \in \mathbb{R}$, the lollipop with center $c$, radius $r$ and
stem direction $(\cos\theta, \sin\theta)$ consists of the circle
$\{(x, y) \in \mathbb{R}^2 : (x - a)^2 + (y - b)^2 = r^2\}$ and the stem
$\{c + s(\cos\theta, \sin\theta) : s \ge r\}$, the part of the ray from $c$ in that direction
outside the open disc. For all $c_1, c_2 \in \mathbb{R}^2$, $r_1, r_2 > 0$ and
$\theta_1, \theta_2 \in \mathbb{R}$, consider the lollipops with centers $c_i$, radii $r_i$ and
stem directions $(\cos\theta_i, \sin\theta_i)$. If the number of points where the stem of the
first meets the circle of the second plus the number of points where the stem of the second meets
the circle of the first is $3$ or $4$, then $\cos(\theta_1 - \theta_2) < 0$.

Source: David O. H. Cutler, Jonas Karlsson and Neil J. A. Sloane, *Cutting a Pancake with an
Exotic Knife*, Journal of Integer Sequences 29 (2026), Article 26.4.5, Lemma 3
(`jis-2026-26.4.5-lem-3`), with the definition in the subsection *The lollipop or qoppa*. -/
public theorem cos_sub_neg_of_lollipop_good_pair (c₁ c₂ : ℝ × ℝ) {r₁ r₂ : ℝ}
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (θ₁ θ₂ : ℝ) :
    let circ : ℝ × ℝ → ℝ → Set (ℝ × ℝ) := fun c r =>
      {x | (x.1 - c.1) ^ 2 + (x.2 - c.2) ^ 2 = r ^ 2}
    let stem : ℝ × ℝ → ℝ → ℝ → Set (ℝ × ℝ) := fun c r θ =>
      (fun s : ℝ => c + s • (Real.cos θ, Real.sin θ)) '' Set.Ici r
    (stem c₁ r₁ θ₁ ∩ circ c₂ r₂).ncard + (stem c₂ r₂ θ₂ ∩ circ c₁ r₁).ncard ∈
        ({3, 4} : Set ℕ) → Real.cos (θ₁ - θ₂) < 0 := by
  change (crossings c₁ c₂ r₁ r₂ θ₁).ncard + (crossings c₂ c₁ r₂ r₁ θ₂).ncard ∈ _ → _
  intro h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  have htotal : 3 ≤ (crossings c₁ c₂ r₁ r₂ θ₁).ncard +
      (crossings c₂ c₁ r₂ r₁ θ₂).ncard := by omega
  by_cases hsec : 1 < (crossings c₁ c₂ r₁ r₂ θ₁).ncard
  · exact cos_sub_neg_of_secant hr₁ hr₂ hsec htotal
  · rw [← Real.cos_neg, neg_sub]
    exact cos_sub_neg_of_secant (c := c₂) (d := c₁) hr₂ hr₁ (by omega) (by omega)

end MetaMathlibExt
