/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Poncelet families of periodic orbits of the elliptic billiard

Shared definitions for the WantedExt modules on the invariants of Reznik, Garcia and Koiller, Eighty
New Invariants of N-Periodics in the Elliptic Billiard (arXiv:2004.12497, Table 2): the ellipse in
standard position, its confocal elliptic caustics, and the turning-number-one `N`-periodic orbits
tangent to a fixed caustic, with the caustic contact points and the segment lengths `l_i`, `r_i`.
-/

module

public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

namespace MathlibExt.Dynamics.EllipticBilliardPonceletShared

/-!
The billiard table is the ellipse `x²/a² + y²/b² = 1` with `0 < b < a`, in standard position (the
invariants are unchanged by isometries of the plane). A confocal elliptic caustic is the ellipse
`x²/(a² - λ) + y²/(b² - λ) = 1` with `0 < λ < b²`. An `N`-periodic orbit with turning number one
tangent to that caustic is a closed polygon `P_0 P_1 … P_{N-1}` inscribed in the table, with
vertices `P_i = (a cos tᵢ, b sin tᵢ)` for a strictly increasing sequence of eccentric anomalies with
`t (i + N) = t i + 2π` (so the vertices are distinct and go once around the table), each side `P_i
P_{i+1}` touching the caustic at a point `P''_i` of its interior. A polygon inscribed in the table
whose sides are tangent to a confocal caustic satisfies the reflection law at every vertex (the two
tangents from a point of the table to a confocal conic make equal angles with the table's tangent),
so these are exactly the `N`-periodic billiard orbits with that caustic, i.e. the Poncelet family of
the source. Indices run over `ℕ`; the data are `N`-periodic.

Reznik, Garcia and Koiller found their invariants on this family: their toolbox starts from `N`
vertices spread evenly around the ellipse (arXiv:2004.12497, Section 'Experimental Method'), i.e.
turning number one. Poncelet families of self-intersecting `N`-periodics (turning number greater
than one) are not covered. The OpenConjectures billiard entries define all `N`-periodic orbits
(`OpenProblem5100022.BilliardOrbit`), but WantedExt cannot import OpenConjectures.
-/

/-- The Euclidean distance between two points of the plane (the product `ℝ × ℝ` carries the sup
metric, so the Euclidean length is written out). -/
noncomputable def euclidDist (p q : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2)

/-- The point `(a cos t, b sin t)` of the ellipse `x²/a² + y²/b² = 1` with eccentric anomaly `t`. -/
noncomputable def ellipsePoint (a b t : ℝ) : ℝ × ℝ :=
  (a * Real.cos t, b * Real.sin t)

/-- `p` lies on the confocal caustic `x²/(a² - λ) + y²/(b² - λ) = 1`. -/
def OnCaustic (a b lam : ℝ) (p : ℝ × ℝ) : Prop :=
  p.1 ^ 2 / (a ^ 2 - lam) + p.2 ^ 2 / (b ^ 2 - lam) = 1

/-- An `N`-periodic orbit with turning number one of the billiard in the ellipse
`x²/a² + y²/b² = 1`, all of whose sides are tangent to the confocal caustic
`x²/(a² - λ) + y²/(b² - λ) = 1`. -/
structure PonceletOrbit (a b lam : ℝ) (N : ℕ) where
  /-- The eccentric anomaly of the vertex `P_i`. -/
  anomaly : ℕ → ℝ
  anomaly_strictMono : StrictMono anomaly
  /-- One full turn per period: the vertices `P_0, …, P_{N-1}` are distinct and in cyclic order. -/
  anomaly_add_period : ∀ i, anomaly (i + N) = anomaly i + 2 * Real.pi
  /-- The point `P''_i` where the side `P_i P_{i+1}` touches the caustic. -/
  contact : ℕ → ℝ × ℝ
  contact_onCaustic : ∀ i, OnCaustic a b lam (contact i)
  contact_mem_side : ∀ i, contact i ∈
    openSegment ℝ (ellipsePoint a b (anomaly i)) (ellipsePoint a b (anomaly (i + 1)))
  /-- The side `P_i P_{i+1}` is orthogonal to the caustic's normal `(x/(a² - λ), y/(b² - λ))` at
  `P''_i`, i.e. tangent to the caustic there. -/
  side_tangent : ∀ i,
    (contact i).1 / (a ^ 2 - lam) *
        ((ellipsePoint a b (anomaly (i + 1))).1 - (ellipsePoint a b (anomaly i)).1) +
      (contact i).2 / (b ^ 2 - lam) *
        ((ellipsePoint a b (anomaly (i + 1))).2 - (ellipsePoint a b (anomaly i)).2) = 0

namespace PonceletOrbit

variable {a b lam : ℝ} {N : ℕ}

/-- The vertex `P_i` of the orbit. -/
noncomputable def vertex (O : PonceletOrbit a b lam N) (i : ℕ) : ℝ × ℝ :=
  ellipsePoint a b (O.anomaly i)

/-- `l_i = |P''_i - P_i|`, the part of the side `P_i P_{i+1}` before the caustic contact
point. -/
noncomputable def l (O : PonceletOrbit a b lam N) (i : ℕ) : ℝ :=
  euclidDist (O.contact i) (O.vertex i)

/-- `r_i = |P_{i+1} - P''_i|`, the part of the side `P_i P_{i+1}` after the caustic contact
point. -/
noncomputable def r (O : PonceletOrbit a b lam N) (i : ℕ) : ℝ :=
  euclidDist (O.vertex (i + 1)) (O.contact i)

/-- The perimeter `L` of the orbit. -/
noncomputable def perimeter (O : PonceletOrbit a b lam N) : ℝ :=
  ∑ i ∈ Finset.range N, euclidDist (O.vertex i) (O.vertex (i + 1))

end PonceletOrbit

end MathlibExt.Dynamics.EllipticBilliardPonceletShared
