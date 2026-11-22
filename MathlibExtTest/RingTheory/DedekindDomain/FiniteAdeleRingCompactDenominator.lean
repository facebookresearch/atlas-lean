/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.FiniteAdeleRingCompactDenominator

/-! # Consumers for a compact-set denominator in the finite adele ring -/

namespace FiniteAdeleRingCompactDenominatorTest

open IsDedekindDomain

/-- The exact source statement, with the original binders. -/
public theorem exactSource (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {C : Set (IsDedekindDomain.FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ C, ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (algebraMap R (IsDedekindDomain.FiniteAdeleRing R K) s * y) v
        ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v :=
  IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
    R K hC

/-- Boundary example: the empty set is compact, and the conclusion still
produces a nonzero denominator (compactness is not vacuous here). -/
public theorem exactSource_empty (R K : Type*) [CommRing R] [IsDedekindDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    ∃ s : R, s ≠ 0 ∧ ∀ y ∈ (∅ : Set (IsDedekindDomain.FiniteAdeleRing R K)),
      ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      (algebraMap R (IsDedekindDomain.FiniteAdeleRing R K) s * y) v
        ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers K v :=
  IsDedekindDomain.FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
    R K isCompact_empty

end FiniteAdeleRingCompactDenominatorTest
