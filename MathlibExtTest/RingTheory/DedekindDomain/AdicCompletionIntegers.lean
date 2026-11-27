/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import MathlibExt.RingTheory.DedekindDomain.AdicCompletionIntegers

@[expose] public section

open IsDedekindDomain

namespace MathlibExtTest.RingTheory.DedekindDomain.AdicCompletionIntegers

variable {A K : Type*} [CommRing A] [IsDedekindDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

example (v : HeightOneSpectrum A) :
    Ideal.map (algebraMap A ↥(v.adicCompletionIntegers K)) v.asIdeal =
      IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K) :=
  v.map_asIdeal_eq_maximalIdeal

noncomputable example (p : Nat.Primes) :
    let v := (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p
    Ideal.map (algebraMap ℤ ↥(v.adicCompletionIntegers ℚ)) v.asIdeal =
      IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ) := by
  intro v
  exact HeightOneSpectrum.map_asIdeal_eq_maximalIdeal v

example : Prime (Ideal.span {(2 : ℤ)}) := by
  have hne : (2 : ℤ) ≠ 0 := by norm_num
  have hI : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hne).mpr (Nat.prime_iff_prime_int.mp (by decide))
  exact Ideal.prime_of_isPrime (by rwa [Ne, Ideal.span_singleton_eq_bot]) hI

example (h2 : Prime (Ideal.span {(2 : ℤ)})) :
    (algebraMap ℤ ↥((HeightOneSpectrum.ofPrime h2).adicCompletionIntegers ℚ)) 2 ∈
      IsLocalRing.maximalIdeal ↥((HeightOneSpectrum.ofPrime h2).adicCompletionIntegers ℚ) := by
  rw [← HeightOneSpectrum.map_asIdeal_eq_maximalIdeal]
  refine Ideal.mem_map_of_mem _ ?_
  rw [HeightOneSpectrum.ofPrime_asIdeal]
  exact Ideal.mem_span_singleton_self 2

-- Consumer with the original binders: an arbitrary Dedekind domain, not
-- only a number field.
example (v : HeightOneSpectrum A) :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K))
      ↥(v.adicCompletionIntegers K) :=
  v.adicCompletionIntegers_isAdicComplete

-- Higher-universe consumer.
example {A' : Type (max 3 5)} {K' : Type (max 1 7)} [CommRing A'] [IsDedekindDomain A']
    [Field K'] [Algebra A' K'] [IsFractionRing A' K'] (v : HeightOneSpectrum A') :
    IsAdicComplete (IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers K'))
      ↥(v.adicCompletionIntegers K') :=
  v.adicCompletionIntegers_isAdicComplete

end MathlibExtTest.RingTheory.DedekindDomain.AdicCompletionIntegers

