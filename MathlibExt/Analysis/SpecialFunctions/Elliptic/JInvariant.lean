/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

/-!
# The $j$-invariant of a period lattice

For a period pair `L`, `PeriodPair.jInvariant L` is the $j$-invariant
$1728\, g_2^3 / (g_2^3 - 27\, g_3^2)$ of its lattice, with `PeriodPair.g₂` and `PeriodPair.g₃`
the Eisenstein invariants of the lattice.

The source is Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT
OpenCourseWare, Fall 2025, Lecture 15, Definition 15.2, p. 3.
-/

@[expose] public section

set_option autoImplicit false

namespace PeriodPair

/-- The $j$-invariant of the lattice of a period pair `L`,

$$j(L) = 1728\, \frac{g_2(L)^3}{g_2(L)^3 - 27\, g_3(L)^2},$$

with `g₂ L = 60 G₄(L)` and `g₃ L = 140 G₆(L)` the Eisenstein invariants of the lattice. The
denominator is the discriminant of the lattice; the definition does not use that it is
nonzero.

Source: Andrew V. Sutherland, *18.783 Elliptic Curves*, lecture notes, MIT OpenCourseWare,
Fall 2025, Lecture 15, Definition 15.2, p. 3. -/
noncomputable def jInvariant (L : PeriodPair) : ℂ :=
  1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)

end PeriodPair
