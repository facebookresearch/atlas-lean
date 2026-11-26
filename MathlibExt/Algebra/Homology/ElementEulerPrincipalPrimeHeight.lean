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

public import MathlibExt.Algebra.Homology.ElementEulerPrimeFiltration
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height of prime factors of a principal quotient

Let R be noetherian and local, let a be a non-zero-divisor, and let b lie in the maximal
ideal. For a prime decomposition of the Euler invariant on R/(a), with support dimension at
most one, every factor prime excluding b has height one.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u

namespace Module

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- A contributing factor of a regular principal quotient has height one.

For a ∈ nonZeroDivisors R, b in the maximal ideal and the stated support-dimension bound, a
prime factor of the decomposition of R/(a) that excludes b has ideal height 1. -/
theorem ElementEulerPrimeDecomposition.factor_prime_height_eq_one_of_principal
    {a b : R} (d : ElementEulerPrimeDecomposition R (R ⧸ Ideal.span {a}) b)
    (ha : a ∈ nonZeroDivisors R) (hb : b ∈ IsLocalRing.maximalIdeal R)
    (hdim : Module.supportDim R (R ⧸ Ideal.span {a}) ≤ 1)
    (factor : ElementEulerPrimeFactor R b) (hf : factor ∈ d.factors)
    (hbf : b ∉ factor.prime.asIdeal) : factor.prime.asIdeal.height = 1 := by
  let I : Ideal R := Ideal.span {a}
  have hIp : I ≤ factor.prime.asIdeal := by
    simpa only [Ideal.annihilator_quotient] using
      Module.mem_support_iff_of_finite.mp (d.factor_mem_support factor hf)
  have hmin := d.factor_minimal_support_of_not_mem_of_supportDim_le_one
    R hb hdim factor hf hbf
  have hminimal : factor.prime.asIdeal ∈ I.minimalPrimes := by
    refine ⟨⟨factor.prime.isPrime, hIp⟩, ?_⟩
    intro J hJ hJp
    let q : PrimeSpectrum R := ⟨J, hJ.1⟩
    have hq : q ∈ Module.support R (R ⧸ I) :=
      Module.mem_support_iff_of_finite.mpr (by
        simpa only [Ideal.annihilator_quotient] using hJ.2)
    have heq := hmin q hq hJp
    exact (congrArg PrimeSpectrum.asIdeal heq).symm.le
  apply le_antisymm
  · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I _ hminimal
  · exact (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha).trans
      (Ideal.height_mono hIp)

end Module
