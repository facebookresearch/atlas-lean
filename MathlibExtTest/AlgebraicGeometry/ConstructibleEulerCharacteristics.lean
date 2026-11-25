/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics

/-!
# Sign convention of the compact-support Euler characteristic

The Euler characteristic is the alternating sum `∑_{n ≤ bound} (-1)^n dim H^n_c`, with the
sign `+` in degree `0` and `-` in degree `1`. A weight pulled back along a map is evaluated on
the image point.
-/

open CategoryTheory
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ConstructibleEulerCharacteristics

example {Z : TopCat.{0}} (B : FiniteCompactBetti Z) (h : B.bound = 1) :
    compactEuler B =
      (Module.finrank ℚ (CompactSupportBetti.Cohomology Z 0) : ℤ) -
        Module.finrank ℚ (CompactSupportBetti.Cohomology Z 1) := by
  simp [compactEuler, h, Finset.sum_range_succ]
  ring

example {Z : TopCat.{0}} (B : FiniteOrdinaryBetti Z) (h : B.bound = 0) :
    ordinaryEuler B = Module.finrank ℚ (BettiRealization.Cohomology Z ((0 : ℕ) : ℤ)) := by
  simp [ordinaryEuler, h]

example {X Y : PerverseSheaves.ComplexScheme} (g : X ⟶ Y) (f : ComplexAnalytification.space Y → ℤ)
    (p : ComplexAnalytification.space X) :
    pulledWeight g f p = f (ComplexAnalytification.spaceMap g p) := rfl
