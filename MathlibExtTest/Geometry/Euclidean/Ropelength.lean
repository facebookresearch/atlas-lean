/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.Euclidean.Ropelength

@[expose] public section

namespace RopelengthTest

open MathlibExt.Geometry.Euclidean.Ropelength

/-- For the vertices of a Mathlib triangle, the total extension returns
the ordinary circumradius. -/
example (t : Affine.Triangle ℝ R3) :
    circumradiusENN (t.points 0) (t.points 1) (t.points 2) =
      ENNReal.ofReal t.circumradius :=
  circumradiusENN_eq_ofReal_circumradius t rfl rfl rfl

/-- Three points of a triangle lying on the unit sphere about a center
in their affine span have extended circumradius one. -/
example (t : Affine.Triangle ℝ R3) (c : R3)
    (hc : c ∈ affineSpan ℝ (Set.range t.points))
    (h : ∀ i, dist (t.points i) c = 1) :
    circumradiusENN (t.points 0) (t.points 1) (t.points 2) = 1 := by
  rw [circumradiusENN_eq_ofReal_circumradius t rfl rfl rfl,
    ← Affine.Simplex.eq_circumradius_of_dist_eq t hc h]
  simp

/-- A collinear triple has infinite extended circumradius. -/
example {p q r : R3} (h : Collinear ℝ ({p, q, r} : Set R3)) :
    circumradiusENN p q r = ⊤ :=
  circumradiusENN_eq_top_of_collinear h

/-- A coincident triple is likewise degenerate. -/
example (p q : R3) : circumradiusENN p p q = ⊤ :=
  circumradiusENN_eq_top_of_eq_left rfl

/-- Swapping and reversing arguments do not change the radius. -/
example (p q r : R3) :
    circumradiusENN q p r = circumradiusENN p q r ∧
      circumradiusENN p r q = circumradiusENN p q r ∧
        circumradiusENN r q p = circumradiusENN p q r :=
  ⟨circumradiusENN_swap_left p q r, circumradiusENN_swap_right p q r,
    circumradiusENN_reverse p q r⟩

/-- Translation does not change the radius. -/
example (v p q r : R3) :
    circumradiusENN (v +ᵥ p) (v +ᵥ q) (v +ᵥ r) =
      circumradiusENN p q r :=
  circumradiusENN_vadd v p q r

/-- Thickness is bounded by every sampled triple and decreases when the
set grows. -/
example {s t : Set R3} (hst : s ⊆ t) {p q r : R3}
    (hp : p ∈ s) (hq : q ∈ s) (hr : r ∈ s) :
    thickness t ≤ circumradiusENN p q r :=
  (thickness_anti hst).trans (thickness_le hp hq hr)

/-- Empty and singleton sets have infinite thickness. -/
example (p : R3) :
    thickness (∅ : Set R3) = ⊤ ∧ thickness {p} = ⊤ :=
  ⟨thickness_empty, thickness_singleton p⟩

/-- For a `C¹` curve, contour length is the integral of speed. -/
example {γ : ℝ → R3} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    contourLength γ a b =
      ENNReal.ofReal (∫ t in a..b, ‖deriv γ t‖) :=
  contourLength_eq_ofReal_integral_norm_deriv hab hγ

/-- The ratio is, by definition, contour length over the thickness of
the whole trace. -/
example (γ : ℝ → R3) (a b : ℝ) :
    ropelengthRatio γ a b =
      contourLength γ a b / thickness (γ '' Set.Icc a b) :=
  rfl

end RopelengthTest
