/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import MathlibExt.RingTheory.DedekindDomain.FiniteSupport

@[expose] public section

open IsDedekindDomain

open scoped nonZeroDivisors

namespace MathlibExtTest.RingTheory.DedekindDomain.FiniteSupport

/-- Lemma 3.6 at `ℤ`: only finitely many prime ideals of `ℤ` contain `6`. -/
example : Set.Finite {P : Ideal ℤ | P.IsPrime ∧ (6 : ℤ) ∈ P} :=
  Ideal.finite_setOf_isPrime_and_mem (by norm_num)

/-- Corollary 3.7 at `ℤ`: only finitely many prime ideals of `ℤ` contain `(6)`. -/
example : {p : Ideal ℤ | p.IsPrime ∧ Ideal.span {(6 : ℤ)} ≤ p}.Finite :=
  Ideal.finite_setOf_isPrime_and_le (by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num)

/-- The prime `(5)` is prime in `ℤ`. -/
private theorem prime_span_five : (Ideal.span {(5 : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by norm_num : (5 : ℤ) ≠ 0)]
  exact Nat.prime_iff_prime_int.mp (by decide)

/-- `(6)` is not contained in `(5)`, since `5 ∤ 6`. -/
private theorem not_span_six_le_span_five :
    ¬ (Ideal.span {(6 : ℤ)} ≤ Ideal.span {(5 : ℤ)}) := by
  intro h
  have hmem : (6 : ℤ) ∈ Ideal.span {(5 : ℤ)} :=
    h (Ideal.mem_span_singleton_self 6)
  rw [Ideal.mem_span_singleton'] at hmem
  obtain ⟨a, ha⟩ := hmem
  omega

/-- Lemma 3.9 at `ℤ`: the multiplicity of `(5)` in the factorization of `(6)`
is zero, since `(5)` does not contain `(6)`. -/
example : Multiset.count (Ideal.span {(5 : ℤ)})
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(6 : ℤ)})) = 0 :=
  (Ideal.count_normalizedFactors_eq_zero_iff prime_span_five (by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    norm_num)).mpr not_span_six_le_span_five

/-- Corollary 3.10 at `ℤ`: the valuations of the fractional ideal `(6)` vanish
at all but finitely many height-one primes. -/
example : {v : HeightOneSpectrum ℤ |
    FractionalIdeal.count ℚ v
      (↑(Ideal.span {(6 : ℤ)}) : FractionalIdeal ℤ⁰ ℚ) ≠ 0}.Finite :=
  FractionalIdeal.count_eq_zero_for_all_but_finitely_many _

/-- The height-one primes of `ℤ` above `2` and `5`, via `primesEquiv`. -/
private noncomputable def vTwo : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨2, by decide⟩

/-- The height-one prime of `ℤ` above `5`. -/
private noncomputable def vFive : HeightOneSpectrum ℤ :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm ⟨5, by decide⟩

private theorem vTwo_ne_vFive : vTwo ≠ vFive := by
  intro h
  have hcongr := congrArg (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)) h
  rw [show Rat.HeightOneSpectrum.primesEquiv (R := ℤ) vTwo =
        (⟨2, by decide⟩ : Nat.Primes) from Equiv.apply_symm_apply _ _,
      show Rat.HeightOneSpectrum.primesEquiv (R := ℤ) vFive =
        (⟨5, by decide⟩ : Nat.Primes) from Equiv.apply_symm_apply _ _] at hcongr
  exact absurd (congrArg Subtype.val hcongr) (by norm_num)

/-- A concrete valuation: `val₅((2)) = 0`, since `(2) ≠ (5)`. -/
example : FractionalIdeal.count ℚ vFive
    (↑(vTwo.asIdeal) : FractionalIdeal ℤ⁰ ℚ) = 0 :=
  FractionalIdeal.count_maximal_coprime ℚ vFive vTwo_ne_vFive

/-- A concrete valuation: `val₂((2)) = 1`. -/
example : FractionalIdeal.count ℚ vTwo
    (↑(vTwo.asIdeal) : FractionalIdeal ℤ⁰ ℚ) = 1 :=
  FractionalIdeal.count_self ℚ vTwo

end MathlibExtTest.RingTheory.DedekindDomain.FiniteSupport
