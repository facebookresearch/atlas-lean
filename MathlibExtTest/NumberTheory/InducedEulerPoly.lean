/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.InducedEulerPoly

@[expose] public section

set_option autoImplicit false

open IsDedekindDomain NumberField

/-- Exact-source consumer, using the original binders verbatim. -/
example (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (s Z : ℂ)
    (h : HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) Z) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) Z :=
  NumberField.hasProd_inv_eval_inducedEulerPoly_of_hasProd F K c s Z h

/-- The same consumer in a higher universe. -/
example (F K : Type 1) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)]
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (s Z : ℂ)
    (h : HasProd (fun 𝔓 : HeightOneSpectrum (𝓞 K) =>
      (1 - c 𝔓 * ((Ideal.absNorm 𝔓.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) Z) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F c p).eval (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) Z :=
  NumberField.hasProd_inv_eval_inducedEulerPoly_of_hasProd F K c s Z h

/-- Boundary example: with `c = 0` every local factor is `1`, so the regrouped
product is the constant product `1`; the hypothesis cannot be dropped to a
single prime. -/
example (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra (𝓞 F) (𝓞 K)] [Algebra.IsIntegral (𝓞 F) (𝓞 K)] (s : ℂ) :
    HasProd (fun p : HeightOneSpectrum (𝓞 F) =>
      ((inducedEulerPoly F (fun _ : HeightOneSpectrum (𝓞 K) => (0 : ℂ)) p).eval
        (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) 1 := by
  apply NumberField.hasProd_inv_eval_inducedEulerPoly_of_hasProd F K
    (fun _ : HeightOneSpectrum (𝓞 K) => (0 : ℂ)) s 1
  simpa using hasProd_const_one (α := HeightOneSpectrum (𝓞 K)) (β := ℂ)
