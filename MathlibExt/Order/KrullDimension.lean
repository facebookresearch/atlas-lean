/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ringKrullDim_le_of_ringHom_isIntegral.lean` and
`P2M/Sol/S_ringKrullDim_le_of_ringHom_isIntegral.lean`
(fermats-last-theorem):
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The source is machine-generated proof code built around a proof-extraction
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Krull dimension under integral homomorphisms

An integral ring homomorphism cannot increase Krull dimension: contraction
of prime ideals is strictly monotone along it, since an integral element
distinguishing two primes pulls back to distinguish their contractions.
-/

@[expose] public section

universe u v

/-- An integral ring homomorphism does not increase Krull dimension. -/
theorem ringKrullDim_le_of_ringHom_isIntegral {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.under R < Q.asIdeal.under R
  exact Ideal.under_lt_under_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)
