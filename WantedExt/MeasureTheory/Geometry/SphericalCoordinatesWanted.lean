/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.Geometry.SphericalCoordinatesWanted

/-- **Change of variables to spherical coordinates.** Let $E$ be a real Banach space and let
$f \colon \mathbb{R}^3 \to E$ be any function. Then the integral of $f$ over $\mathbb{R}^3$
equals the integral over the set of $(r, \theta, \varphi) \in \mathbb{R}^3$ with $r > 0$,
$0 < \theta < 2\pi$ and $0 < \varphi < \pi$ of
$r^2 \sin\varphi \cdot f(r \sin\varphi \cos\theta,\, r \sin\varphi \sin\theta,\, r \cos\varphi)$,
both integrals being Bochner integrals with respect to Lebesgue measure.

No integrability hypothesis is assumed; as usual for Bochner integrals, a non-integrable
function has integral $0$. This is the three-dimensional analogue of the polar-coordinate
change of variables.

Sources:
- Mathlib `docs/undergrad.yaml`, section "Measures and integral calculus /
  Integration", entry "change of variables to spherical co-ordinates"
  (currently missing: empty entry, no Mathlib declaration).
- W. Rudin, *Real and Complex Analysis*, 3rd ed., Ch. 8, Exercise 4 (spherical
  coordinates in `ℝ³`).
- https://en.wikipedia.org/wiki/Spherical_coordinate_system#Integration_and_differentiation_in_spherical_coordinates
-/
public theorem_wanted integral_comp_spherical_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ × ℝ × ℝ → E) :
    (∫ p in {p : ℝ × ℝ × ℝ |
        0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < 2 * Real.pi ∧ 0 < p.2.2 ∧ p.2.2 < Real.pi},
      (p.1 ^ 2 * Real.sin p.2.2 : ℝ) •
        f (p.1 * Real.sin p.2.2 * Real.cos p.2.1,
          p.1 * Real.sin p.2.2 * Real.sin p.2.1, p.1 * Real.cos p.2.2)) =
      ∫ p, f p

end MathlibExt.MeasureTheory.Geometry.SphericalCoordinatesWanted
