/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.JetArcFunctors
import Mathlib.Algebra.Polynomial.Div

/-!
The first-order parameter is nonzero but its square vanishes. The zeroth
disc kills that parameter. These distinguish the actual nilpotent jet
test rings from their reduced point sets and check the n+1 convention.
-/

open MathlibExt.AlgebraicGeometry.JetArcFunctors

example : parameter ℤ 0 = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simp [augmentationIdeal]

example : parameter ℤ 1 ^ 2 = 0 := by
  change (Ideal.Quotient.mk (augmentationIdeal ℤ ^ 2) Polynomial.X) ^ 2 = 0
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.pow_mem_pow (Ideal.subset_span (by simp)) 2

example : parameter ℤ 1 ≠ 0 := by
  intro h
  have hmem : Polynomial.X ∈ (augmentationIdeal ℤ) ^ 2 :=
    Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [augmentationIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    Polynomial.X_pow_dvd_iff] at hmem
  have hz := hmem 1 (by decide)
  norm_num at hz

example : truncationRing ℤ (show 0 ≤ 1 by decide) (parameter ℤ 1) = 0 := by
  change parameter ℤ 0 = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simp [augmentationIdeal]
