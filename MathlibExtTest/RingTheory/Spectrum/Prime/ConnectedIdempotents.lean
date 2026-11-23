/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Spectrum.Prime.ConnectedIdempotents

@[expose] public section

-- Consumer with the original binders.
universe u in
example (R : Type u) [CommRing R] [IsNoetherianRing R] :
    ∃ (m : ℕ) (e : Fin m → R), CompleteOrthogonalIdempotents e ∧
      ∀ i, ConnectedSpace (PrimeSpectrum (Localization.Away (e i))) :=
  IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum R

-- Higher-universe consumer: the statement is universe-polymorphic.
example (R : Type 1) [CommRing R] [IsNoetherianRing R] :
    ∃ (m : ℕ) (e : Fin m → R), CompleteOrthogonalIdempotents e ∧
      ∀ i, ConnectedSpace (PrimeSpectrum (Localization.Away (e i))) :=
  IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum R

-- Boundary: the decomposition also exists for a disconnected spectrum,
-- here the product of two fields.
example :
    ∃ (m : ℕ) (e : Fin m → (ℚ × ℚ)), CompleteOrthogonalIdempotents e ∧
      ∀ i, ConnectedSpace (PrimeSpectrum (Localization.Away (e i))) :=
  IsNoetherianRing.exists_completeOrthogonalIdempotents_forall_connectedSpace_primeSpectrum (ℚ × ℚ)
