/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.RingTheory.Length.FiniteFractionSubalgebra
public import MathlibExt.RingTheory.Artinian.LocalScalarLength

/-!
# Actual local multiplicities of finite birational principal quotients

A nonzero scalar quotient of a finite subalgebra in the prescribed
fraction field of a one-dimensional Noetherian domain is genuinely
Artinian. Its base-ring length agrees with the original principal quotient
and decomposes into the true local nilpotent lengths and residue-field
degrees. The residue degrees are measured over the original base residue
field, including nonfaithful scalar quotients.

This is the local principal-divisor coefficient calculation for singular
curves. Both quotient carriers and all local multiplicities are actual
algebraic objects; no divisor pushforward or characteristic-degree formula
is an input.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped BigOperators

universe u v

namespace Subalgebra

variable {R : Type u} [CommRing R] {K : Type v} [Field K] [Algebra R K]
variable (A : Subalgebra R K) [Module.Finite R A]

/-- The actual principal scalar quotient of a finite algebra remains finite over its base ring. -/
local instance principalQuotientFinite (a : R) :
    Module.Finite R (A ⧸ Ideal.span {algebraMap R A a}) :=
  Module.Finite.of_surjective
    (IsScalarTower.toAlgHom R A (A ⧸ Ideal.span {algebraMap R A a})).toLinearMap
    Ideal.Quotient.mk_surjective

variable [IsDomain R] [IsFractionRing R K] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]

/-- The genuine nonzero scalar quotient of a finite birational algebra is Artinian. -/
theorem isArtinian_quotient_span_of_finite {a : R} (ha : a ≠ 0) :
    IsArtinianRing (A ⧸ Ideal.span {algebraMap R A a}) := by
  let Q := A ⧸ Ideal.span {algebraMap R A a}
  have hl : Module.length R Q ≠ ⊤ := by
    rw [← length_quotient_span_eq_of_finite A ha]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_iff_ne_zero.mpr ha))
  have hArt : IsArtinian R Q :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp hl)).2
  let _ : IsArtinian R Q := hArt
  exact isArtinian_of_tower R hArt

variable [IsLocalRing R]

/-- The original principal-quotient length is the actual residue-weighted sum of local birational quotient
multiplicities. -/
theorem length_toNat_quotient_span_eq_sum_primeSpectrum {a : R} (ha : a ≠ 0) :
    letI : IsArtinianRing (A ⧸ Ideal.span {algebraMap R A a}) :=
      isArtinian_quotient_span_of_finite A ha
    letI : Fintype (PrimeSpectrum (A ⧸ Ideal.span {algebraMap R A a})) :=
      Fintype.ofFinite (PrimeSpectrum (A ⧸ Ideal.span {algebraMap R A a}))
    (Module.length R (R ⧸ Ideal.span {a})).toNat =
      ∑ p : PrimeSpectrum (A ⧸ Ideal.span {algebraMap R A a}),
        (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
          IsArtinianRing.residueDegreeAtPrime R (A ⧸ Ideal.span {algebraMap R A a}) p := by
  let _ : IsArtinianRing (A ⧸ Ideal.span {algebraMap R A a}) :=
    isArtinian_quotient_span_of_finite A ha
  let _ : Fintype (PrimeSpectrum (A ⧸ Ideal.span {algebraMap R A a})) :=
    Fintype.ofFinite (PrimeSpectrum (A ⧸ Ideal.span {algebraMap R A a}))
  rw [length_quotient_span_eq_of_finite A ha]
  exact IsArtinianRing.length_toNat_eq_sum_primeSpectrum_mul_residueDegree R
    (A ⧸ Ideal.span {algebraMap R A a})

end Subalgebra
