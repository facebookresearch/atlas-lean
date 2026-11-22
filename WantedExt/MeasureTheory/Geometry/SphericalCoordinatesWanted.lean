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

/-- Change of variables to spherical coordinates in `ℝ³`: the integral of `f`
over all of space equals the integral over `(r, θ, φ)` with `r > 0`,
`0 < θ < 2π`, `0 < φ < π` of `f` at
`(r sin φ cos θ, r sin φ sin θ, r cos φ)` against the Jacobian `r² sin φ`.
This mirrors the polar-coordinate formula `integral_comp_polarCoord_symm`.

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
