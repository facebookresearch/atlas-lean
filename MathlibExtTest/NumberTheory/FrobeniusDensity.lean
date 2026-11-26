/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.FrobeniusDensity
import Mathlib.RingTheory.Ideal.Int

@[expose] public section

open Filter Topology Asymptotics

/-- Exact-source consumer for the degree-one asymptotic statement. -/
theorem exactSource_degOneAsymptotic (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L :=
  FrobeniusDensity.degOneAsymptotic L

/-- Exact-source consumer for the prime-sum logarithmic pole. -/
theorem exactSource_primeSum (K : Type*) [Field K] [NumberField K] :
    (fun s : ℝ => (FrobeniusDensity.primeSum K s).toReal + Real.log (s - 1))
      =O[nhdsWithin 1 (Set.Ioi 1)] (fun _ => (1 : ℝ)) :=
  FrobeniusDensity.primeSum_toReal_add_log_isBigO K

/-- `degOneCount` vanishes at a natural number that is not prime. -/
example (K : Type*) [Field K] [NumberField K] : FrobeniusDensity.degOneCount K 4 = 0 :=
  FrobeniusDensity.degOneCount_of_not_prime K (by decide)

/-- At a prime `ℓ`, `degOneCount K ℓ` counts some of the primes of `𝓞 K` over `ℓ`, so it is at
most the degree `[K : ℚ]`. -/
example (K : Type*) [Field K] [NumberField K] {ℓ : ℕ} (hℓ : ℓ.Prime) :
    FrobeniusDensity.degOneCount K ℓ ≤ Module.finrank ℚ K := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [FrobeniusDensity.degOneCount_of_prime K hℓ]
  refine (Set.ncard_le_ncard (Set.sep_subset _ _)).trans ?_
  have :=
    Fintype.ofFinite ((FrobeniusDensity.ratPrimeIdeal ℓ).primesOver (NumberField.RingOfIntegers K))
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones,
    ← NumberField.RingOfIntegers.rank K, ← Ideal.sum_ramification_inertia_eq_finrank
      (FrobeniusDensity.ratPrimeIdeal ℓ) (NumberField.RingOfIntegers K)]
  refine Finset.sum_le_sum fun q _ => ?_
  have := q.2.1
  have := q.2.2
  exact Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
