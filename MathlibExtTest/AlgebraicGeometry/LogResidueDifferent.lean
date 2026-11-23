/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.LogResidueDifferent

/-!
# Tests for the affine conductor

The conductor of a ring in itself is the unit ideal; the conductor of `R` in `R[X]` is zero,
since `r * X` is a constant only when `r = 0`.
-/

open MathlibExt.AlgebraicGeometry.LogResidueDifferent Polynomial

variable (R : Type) [CommRing R]

example : ringConductor (RingHom.id R) = ⊤ := by
  refine eq_top_iff.mpr fun a _ ↦ ?_
  intro b
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨C (a * b), by simp⟩

example [Nontrivial R] : ringConductor (C : R →+* R[X]) = ⊥ := by
  refine eq_bot_iff.mpr fun r hr ↦ ?_
  have hX := hr X
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hX
  obtain ⟨q, hq⟩ := hX
  have h1 := congrArg (coeff · 1) hq
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_def, eval₂_at_zero,
    RingHom.algebraMap_toAlgebra, coeff_C, coeff_C_mul_X] at h1
  rw [Ideal.mem_bot]
  simpa using h1.symm
