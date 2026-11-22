/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.GoingUp

public import Mathlib.RingTheory.IntegralClosure.Algebra.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

@[expose] public section

/-- Krull dimension cannot increase along an integral extension of commutative rings.

This is the dimension consequence of strict contraction of prime ideals
(`Ideal.IsIntegral.comap_lt_comap`): contraction gives a strictly monotone map
`PrimeSpectrum B → PrimeSpectrum A`, hence the inequality of Krull dimensions. -/
theorem ringKrullDim_le_of_integral {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] : ringKrullDim B ≤ ringKrullDim A :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B))
    (fun _ _ h => Ideal.IsIntegral.under_lt_under h)

/-- Every finite chain of prime ideals lifts along an injective integral algebra map. -/
theorem exists_ltSeries_of_integral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    (p : LTSeries (PrimeSpectrum A)) :
    ∃ q : LTSeries (PrimeSpectrum B),
      q.length = p.length ∧
        List.map (PrimeSpectrum.comap (algebraMap A B)) q.toList = p.toList := by
  have := p.head.isPrime
  have hbot : (⊥ : Ideal B).under A ≤ p.head.asIdeal := by
    change (⊥ : Ideal B).comap (algebraMap A B) ≤ p.head.asIdeal
    rw [Ideal.comap_bot_of_injective _ hinj]
    exact bot_le
  obtain ⟨Q, -, hQ, hQc⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral p.head.asIdeal (⊥ : Ideal B) hbot
  let _ : Q.IsPrime := hQ
  let _ : Q.LiesOver p.head.asIdeal := ⟨hQc.symm⟩
  obtain ⟨q, hlength, -, hmap⟩ := Ideal.exists_ltSeries_of_hasGoingUp p Q
  exact ⟨q, hlength, hmap⟩

/-- Krull dimension cannot decrease along an injective integral algebra map. -/
theorem ringKrullDim_ge_of_integral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hq, -⟩ := exists_ltSeries_of_integral_of_injective hinj p
  rw [← hq]
  exact le_iSup (fun q : LTSeries (PrimeSpectrum B) => (q.length : WithBot ℕ∞)) q

/-- An injective integral algebra map preserves Krull dimension. -/
theorem ringKrullDim_eq_of_integral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A :=
  le_antisymm ringKrullDim_le_of_integral
    (ringKrullDim_ge_of_integral_of_injective hinj)
