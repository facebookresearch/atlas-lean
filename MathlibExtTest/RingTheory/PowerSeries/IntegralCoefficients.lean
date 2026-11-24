/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.IntegralCoefficients

@[expose] public section

-- Consumer with the original binders.
example
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (g : PowerSeries K) (Φ : Polynomial (PowerSeries R)) (hΦ : Φ.Monic)
    (hroot : Polynomial.eval₂ (PowerSeries.map (algebraMap R K)) g Φ = 0)
    (h : PowerSeries R) (h0 : h ≠ 0)
    (hmul : PowerSeries.map (algebraMap R K) h * g ∈
      (PowerSeries.map (algebraMap R K)).range) :
    g ∈ (PowerSeries.map (algebraMap R K)).range :=
  PowerSeries.mem_range_map_of_monic_of_mul_mem_range g Φ hΦ hroot h h0 hmul

-- The nonzero denominator hypothesis matters: with `h = 0` the conclusion
-- would assert that every integral series descends, with no control at all.
example
    {R K : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (g : PowerSeries K) :
    PowerSeries.map (algebraMap R K) (0 : PowerSeries R) * g ∈
      (PowerSeries.map (algebraMap R K)).range :=
  ⟨0, by simp⟩
