/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Int.Basic
public import MathlibExt.RingTheory.DedekindDomain.QuotientPIRConverse

@[expose] public section

/-!
# Tests for the converse characterizations of Dedekind domains
-/

/-- The quotient-PIR hypothesis holds for `ℤ`, since `ℤ` is a PIR and
quotients of PIRs are PIRs. -/
theorem test_int_quotient_pir (I : Ideal ℤ) (_hI : I ≠ ⊥) :
    IsPrincipalIdealRing (ℤ ⧸ I) :=
  IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-- Smoke test: the converse theorem recovers `IsDedekindDomain ℤ` from the
quotient-PIR hypothesis. -/
theorem test_int_isDedekindDomain_of_quotient_pir : IsDedekindDomain ℤ :=
  isDedekindDomain_of_forall_isPrincipalIdealRing_quotient test_int_quotient_pir

/-- The two-generator hypothesis holds for `ℤ`: every ideal is principal,
so with `I = (g)` any `a ∈ I` gives `I = (a, g)`. -/
theorem test_int_exists_span_pair (I : Ideal ℤ) (a : ℤ) (_hI : I ≠ ⊥) (_ha : a ≠ 0)
    (haI : a ∈ I) : ∃ b : ℤ, I = Ideal.span {a, b} := by
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal I
  refine ⟨g, le_antisymm ?_ ?_⟩
  · rw [hg]
    apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.subset_span (by simp)
  · rw [hg]
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | h
    · rw [hg] at haI
      exact haI
    · rw [Set.mem_singleton_iff.mp h]
      exact Ideal.mem_span_singleton_self g

/-- Smoke test: the converse theorem recovers `IsDedekindDomain ℤ` from the
two-generator hypothesis. -/
theorem test_int_isDedekindDomain_of_span_pair : IsDedekindDomain ℤ :=
  isDedekindDomain_of_forall_exists_span_pair test_int_exists_span_pair

/-- `(2)` is prime in `ℤ`, as an instance for the localization below. -/
instance test_int_span_two_isPrime : (Ideal.span ({2} : Set ℤ)).IsPrime := by
  apply Ideal.isPrime_span_singleton_of_prime
  rw [Int.prime_iff_natAbs_prime]
  simpa using Nat.prime_two

/-- Smoke test: the localization of `ℤ` at `(2)` is a DVR, via the
quotient-PIR hypothesis. -/
theorem test_int_localization_atPrime_isDVR :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span ({2} : Set ℤ))) :=
  isDiscreteValuationRing_localization_atPrime_of_forall_isPrincipalIdealRing_quotient
    test_int_quotient_pir (Ideal.span ({2} : Set ℤ))
    (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)
    inferInstance

#print axioms isDedekindDomain_of_forall_isPrincipalIdealRing_quotient
#print axioms isDedekindDomain_of_forall_exists_span_pair
#print axioms isDiscreteValuationRing_localization_atPrime_of_forall_isPrincipalIdealRing_quotient
#print axioms isNoetherianRing_of_forall_isPrincipalIdealRing_quotient
