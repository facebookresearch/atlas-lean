/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import MathlibExt.RingTheory.DedekindDomain.DVRCharacterization

@[expose] public section

/-!
# Tests for the Dedekind / DVR-localization characterizations
-/

/-- Smoke test: Definition 2.10 recovers `IsDedekindDomain ℤ` from
`ℤ` being integrally closed of Krull dimension at most one. -/
theorem test_int_isDedekindDomain : IsDedekindDomain ℤ :=
  (integrallyClosed_dimensionLEOne_iff_isDedekindDomain ℤ).mp
    ⟨inferInstance, inferInstance⟩

/-- Smoke test: the other direction of Definition 2.10 at `ℤ`. -/
theorem test_int_integrallyClosed_dimensionLEOne :
    IsIntegrallyClosed ℤ ∧ Ring.DimensionLEOne ℤ :=
  (integrallyClosed_dimensionLEOne_iff_isDedekindDomain ℤ).mpr inferInstance

/-- The ideal `(2)` of `ℤ` is prime. -/
theorem span_two_isPrime : (Ideal.span ({2} : Set ℤ)).IsPrime :=
  Ideal.isPrime_span_singleton_of_prime (by
    rw [Int.prime_iff_natAbs_prime]; simpa using Nat.prime_two)

/-- Smoke test: Proposition 2.9 at `ℤ` gives that the localization at
the prime `(2)` is a discrete valuation ring. -/
theorem test_int_localization_evalAtTwo_isDVR
    (h2 : (Ideal.span ({2} : Set ℤ)).IsPrime) :
    IsDiscreteValuationRing
      (Localization.AtPrime (Ideal.span ({2} : Set ℤ))) :=
  (isDiscreteValuationRing_localization_atPrime_iff_integrallyClosed_dimensionLEOne
    ℤ).mpr ⟨inferInstance, inferInstance⟩ (Ideal.span ({2} : Set ℤ))
    (by rw [Ne, Ideal.span_singleton_eq_bot]; norm_num)
    h2

/-- The two pieces above combine: the localization of `ℤ` at `(2)` is a
discrete valuation ring. -/
example : True := by
  have _hDVR := test_int_localization_evalAtTwo_isDVR span_two_isPrime
  trivial

/-- The evaluation map `(Polynomial ℤ) → ZMod 2` sending `X` to `0`, used to show
that `(X)` is not maximal in `(Polynomial ℤ)`. -/
def test_evalZeroModTwo : (Polynomial ℤ) →+* ZMod 2 :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) 0

/-- The evaluation map above is surjective. -/
theorem test_evalZeroModTwo_surjective :
    Function.Surjective test_evalZeroModTwo := by
  intro y
  obtain ⟨z, hz⟩ := ZMod.intCast_surjective (n := 2) y
  exact ⟨Polynomial.C z, by simp [test_evalZeroModTwo, hz]⟩

/-- `(X)` is a nonzero prime ideal of `(Polynomial ℤ)` that is not maximal, so
`(Polynomial ℤ)` does not have Krull dimension at most one. -/
theorem test_polynomial_int_not_dimensionLEOne :
    ¬ Ring.DimensionLEOne (Polynomial ℤ) := by
  intro h
  have hXprime : (Ideal.span ({Polynomial.X} : Set (Polynomial ℤ))).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime Polynomial.prime_X
  have hXne : (Ideal.span ({Polynomial.X} : Set (Polynomial ℤ))) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact Polynomial.X_ne_zero
  have hmax := Ring.DimensionLEOne.maximalOfPrime hXne hXprime
  have _hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hkerMax := RingHom.ker_isMaximal_of_surjective test_evalZeroModTwo
    test_evalZeroModTwo_surjective
  have hle : Ideal.span ({Polynomial.X} : Set (Polynomial ℤ)) ≤
      RingHom.ker test_evalZeroModTwo := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    simp [test_evalZeroModTwo]
  have heq : Ideal.span ({Polynomial.X} : Set (Polynomial ℤ)) =
      RingHom.ker test_evalZeroModTwo :=
    hmax.eq_of_le hkerMax.ne_top hle
  have h2ker : (2 : (Polynomial ℤ)) ∈ RingHom.ker test_evalZeroModTwo := by
    rw [RingHom.mem_ker, map_ofNat]
    simpa using ZMod.natCast_self 2
  have h2mem : (2 : (Polynomial ℤ)) ∈
      Ideal.span ({Polynomial.X} : Set (Polynomial ℤ)) := heq ▸ h2ker
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at h2mem
  exact absurd h2mem (by simp)

/-- Smoke test: `(Polynomial ℤ)` is not a Dedekind domain, via Definition 2.10 and
the dimension failure above. -/
theorem test_polynomial_int_not_isDedekindDomain : ¬ IsDedekindDomain (Polynomial ℤ) := by
  intro h
  exact test_polynomial_int_not_dimensionLEOne
    ((integrallyClosed_dimensionLEOne_iff_isDedekindDomain (Polynomial ℤ)).mpr h).2

#print axioms integrallyClosed_dimensionLEOne_iff_isDedekindDomain
#print axioms isDiscreteValuationRing_localization_atPrime_iff_integrallyClosed_dimensionLEOne
