/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.PrimeAdjoinRoot

@[expose] public section

open Polynomial IsLocalRing

-- Consumer with the original binders, restated over `Type*`.
example (q : ℕ) [Fact q.Prime] (hq : 2 ≤ q)
    (W₀ : Type*) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (g : Polynomial (PowerSeries W₀)) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀))
    (hg0 : ∃ u : PowerSeries W₀, IsUnit u ∧
      g.coeff 0 = (q : PowerSeries W₀) * u) :
    Prime g ∧ IsDomain (AdjoinRoot g) :=
  Polynomial.prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
    q hq W₀ hW₀ g hgm hgdeg hgcoeff hg0

universe u

-- The same consumer in a higher universe.
example (q : ℕ) [Fact q.Prime] (hq : 2 ≤ q)
    (W₀ : Type u) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (g : Polynomial (PowerSeries W₀)) (hgm : g.Monic) (hgdeg : g.natDegree = q - 1)
    (hgcoeff : ∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀))
    (hg0 : ∃ u : PowerSeries W₀, IsUnit u ∧
      g.coeff 0 = (q : PowerSeries W₀) * u) :
    Prime g ∧ IsDomain (AdjoinRoot g) :=
  Polynomial.prime_and_isDomain_adjoinRoot_of_monic_of_coeff_mem_maximalIdeal_powerSeries_of_coeff_zero_eq_natCast_mul
    q hq W₀ hW₀ g hgm hgdeg hgcoeff hg0

-- The degree hypothesis matters: for `q = 2` the conclusion pins the degree
-- to `1`; a monic polynomial of degree `0` cannot satisfy it.
example : ¬ (0 : ℕ) = 2 - 1 := by decide
