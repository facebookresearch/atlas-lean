/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Ideal.Norm.RelNormSeparable

@[expose] public section

/-!
# Tests for the separable relative-norm formula
-/

/-- Smoke test: the relative norm of the prime `(2)` in `ℤ` over itself. -/
theorem test_relNorm_eq_pow_inertiaDeg_of_isSeparable_int :
    Ideal.relNorm ℤ (Ideal.span {(2 : ℤ)}) =
      (Ideal.span {(2 : ℤ)}) ^ (Ideal.span {(2 : ℤ)}).inertiaDeg ℤ := by
  have hL : (Ideal.span {(2 : ℤ)}).LiesOver (Ideal.span {(2 : ℤ)}) :=
    Ideal.LiesOver.mk (by rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id])
  have hM : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible
  exact Ideal.relNorm_eq_pow_inertiaDeg_of_isSeparable _ _

#print axioms Ideal.relNorm_eq_pow_inertiaDeg_of_isSeparable
