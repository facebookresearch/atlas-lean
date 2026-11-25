/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.PrincipalIdealQuotient

@[expose] public section

/-!
# Tests for quotients of Dedekind domains by nonzero ideals
-/

/-- Every ideal of the quotient of a Dedekind domain by a nonzero ideal is principal,
via the new instance. -/
theorem test_isPrincipal_quotient {A : Type*} [CommRing A] [IsDedekindDomain A]
    (I : Ideal A) (hI : I ≠ ⊥) (J : Ideal (A ⧸ I)) : J.IsPrincipal := by
  have := IsDedekindDomain.isPrincipalIdealRing_quotient I hI
  exact IsPrincipalIdealRing.principal J

/-- Smoke test: every ideal of `ℤ ⧸ Ideal.span {12}` is principal. -/
theorem test_isPrincipal_zmod_span_twelve
    (J : Ideal (ℤ ⧸ Ideal.span ({12} : Set ℤ))) : J.IsPrincipal := by
  have h12 : Ideal.span ({12} : Set ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num
  have := IsDedekindDomain.isPrincipalIdealRing_quotient _ h12
  exact IsPrincipalIdealRing.principal J

#print axioms IsDedekindDomain.isPrincipalIdealRing_quotient