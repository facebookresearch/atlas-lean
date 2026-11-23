/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.TropicalTorIntersection

/-!
# Tests for Tor intersection coefficients

A vanishing Tor module has length zero, and an intersection with the unit ideal is empty, so its
length coefficient is zero.
-/

open MathlibExt.AlgebraicGeometry.TropicalTorIntersection

/-- Vanishing Tor modules have length zero. -/
example (I J : Ideal ℤ) (q : ℕ) (h : CategoryTheory.Limits.IsZero (torModule ℤ I J q)) :
    Module.length ℤ (torModule ℤ I J q) = 0 :=
  torLength_zero ℤ h

/-- An intersection with the unit ideal has length coefficient zero. -/
example (J : Ideal ℤ) : schemeCoefficient ℤ ⊤ J = 0 := by
  rw [schemeCoefficient, top_sup_eq, Module.length_eq_zero_iff]
  exact Ideal.Quotient.subsingleton_iff.mpr rfl
