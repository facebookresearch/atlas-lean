/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Dedekind domains characterized by discrete valuation localizations

ATLAS `NumberTheoryI`, Proposition 2.9 and the characterization form of
Definition 2.10.

Proposition 2.9 says that for a Noetherian domain `A`, the following are
equivalent:

* (i) for every nonzero prime ideal `P` of `A`, the localization `A_P` is a
  discrete valuation ring;
* (ii) `A` is integrally closed and has Krull dimension at most one.

Definition 2.10 names a Noetherian domain satisfying either (hence both) of
these properties a Dedekind domain. Mathlib's `IsDedekindDomain` is that
notion, but its two packaged characterizations are routed through
`IsDedekindDomain` itself:
`isDedekindDomain_iff_isDiscreteValuationRing_atPrime` carries the Noetherian
hypothesis on the right-hand side, and `isDedekindDomain_iff` states the
integrally-closed/dimension condition with the integrally-closed part spelled
out over a chosen fraction field. This file packages the two book statements
directly: the `(ii) ↔ IsDedekindDomain A` form of Definition 2.10, and the
`(i) ↔ (ii)` equivalence of Proposition 2.9.

The proof follows `v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean`
(`integrallyClosed_dimensionLEOne_iff_isDedekindDomain`,
`isDVR_localization_iff_integrallyClosed_dimensionLEOne`), with v1's custom
`IsDedekindDomainDvr` class replaced by Mathlib's
`isDedekindDomain_iff_isDiscreteValuationRing_atPrime`.
-/

@[expose] public section

/-- Definition 2.10, characterization form: for a Noetherian domain `A`,
`A` is integrally closed of Krull dimension at most one if and only if `A`
is a Dedekind domain. -/
theorem integrallyClosed_dimensionLEOne_iff_isDedekindDomain
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    (IsIntegrallyClosed A ∧ Ring.DimensionLEOne A) ↔ IsDedekindDomain A := by
  constructor
  · intro h
    have hRing : IsDedekindRing A :=
      { toIsNoetherian := inferInstance, toDimensionLEOne := h.2, toIsIntegralClosure := h.1 }
    exact { toIsDomain := inferInstance, toIsDedekindRing := hRing }
  · intro h
    exact ⟨h.toIsDedekindRing.toIsIntegralClosure, h.toIsDedekindRing.toDimensionLEOne⟩

/-- Proposition 2.9: for a Noetherian domain `A`, the localization at every
nonzero prime ideal is a discrete valuation ring if and only if `A` is
integrally closed and has Krull dimension at most one. -/
theorem isDiscreteValuationRing_localization_atPrime_iff_integrallyClosed_dimensionLEOne
    (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] :
    (∀ (P : Ideal A), P ≠ ⊥ → ∀ (_h : P.IsPrime),
      IsDiscreteValuationRing (Localization.AtPrime P)) ↔
    (IsIntegrallyClosed A ∧ Ring.DimensionLEOne A) := by
  constructor
  · intro h
    have hDedekind : IsDedekindDomain A :=
      isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mpr ⟨inferInstance, h⟩
    exact (integrallyClosed_dimensionLEOne_iff_isDedekindDomain A).mpr hDedekind
  · intro h
    have hDedekind : IsDedekindDomain A :=
      (integrallyClosed_dimensionLEOne_iff_isDedekindDomain A).mp h
    intro P hP hPprime
    exact (isDedekindDomain_iff_isDiscreteValuationRing_atPrime.mp hDedekind).2 P hP
      hPprime
