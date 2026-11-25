/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean`
and
`P2M/Sol/S_PowerSeries_mem_range_map_of_monic_of_mul_mem_range.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

@[expose] public section

namespace PowerSeries

private theorem map_algebraMap_injective
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Injective (PowerSeries.map (algebraMap R K)) := by
  intro a b h
  ext n
  apply IsFractionRing.injective R K
  have hcoeff := congrArg (PowerSeries.coeff n) h
  simpa only [PowerSeries.coeff_map] using hcoeff

/-- A power series over the fraction field of a PID which is integral over
`R[[X]]` and which becomes integral after multiplication by a nonzero series
from `R[[X]]` already has coefficients in `R`.

No completeness or locality hypothesis on the PID is used. -/
public theorem mem_range_map_of_monic_of_mul_mem_range
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
    (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
    (h : PowerSeries R) (h0 : h ≠ 0)
    (hmul : PowerSeries.map (algebraMap R K) h * g ∈
      (PowerSeries.map (algebraMap R K)).range) :
    g ∈ (PowerSeries.map (algebraMap R K)).range := by
  classical
  set ι : PowerSeries R →+* PowerSeries K := PowerSeries.map (algebraMap R K) with hι
  let alg' : PowerSeries K →+* FractionRing (PowerSeries K) :=
    algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
  have hι_inj : Function.Injective ι := map_algebraMap_injective
  have halg'_inj : Function.Injective alg' :=
    IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
  have hcomp_inj : Function.Injective (alg'.comp ι) := halg'_inj.comp hι_inj
  let θ : FractionRing (PowerSeries R) →+* FractionRing (PowerSeries K) :=
    IsFractionRing.lift (A := PowerSeries R) (K := FractionRing (PowerSeries R))
      (g := alg'.comp ι) hcomp_inj
  have hθ_alg : ∀ a : PowerSeries R,
      θ (algebraMap (PowerSeries R) (FractionRing (PowerSeries R)) a) = alg' (ι a) :=
    fun a => IsFractionRing.lift_algebraMap hcomp_inj a
  have hθ_comp : θ.comp (algebraMap (PowerSeries R) (FractionRing (PowerSeries R))) =
      alg'.comp ι := RingHom.ext hθ_alg
  have hθ_inj : Function.Injective θ := θ.injective
  obtain ⟨u, hu⟩ := hmul
  set x : FractionRing (PowerSeries R) :=
    algebraMap (PowerSeries R) (FractionRing (PowerSeries R)) u /
      algebraMap (PowerSeries R) (FractionRing (PowerSeries R)) h with hx
  have hιh : ι h ≠ 0 := fun h' => h0 (hι_inj (by rw [h', map_zero]))
  have halg'h : alg' (ι h) ≠ 0 := fun h' => hιh (halg'_inj (by rw [h', map_zero]))
  have hθx : θ x = alg' g := by
    rw [hx, map_div₀, hθ_alg, hθ_alg, div_eq_iff halg'h, ← map_mul, mul_comm, ← hu]
  have hint : IsIntegral (PowerSeries R) x := by
    refine ⟨Φ, hΦ, ?_⟩
    apply hθ_inj
    rw [Polynomial.hom_eval₂, hθ_comp, hθx, map_zero, ← Polynomial.hom_eval₂, hroot,
      map_zero]
  obtain ⟨p, hp⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine ⟨p, halg'_inj ?_⟩
  change alg' (ι p) = alg' g
  rw [← hθ_alg, hp, hθx]

end PowerSeries
