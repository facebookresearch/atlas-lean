/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AdelicFourier

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory
open scoped SchwartzMap

namespace NumberField.AdelicFourier

-- Consumer with the original binders for the Fourier integral.
example {A : Type*} [CommRing A] [MeasurableSpace A] (ψ : AddChar A ℂ)
    (μ : Measure A) (f : A → ℂ) (w : A) :
    fourierIntegral ψ μ f w = ∫ v, ψ (-(v * w)) * f v ∂μ :=
  fourierIntegral_def ψ μ f w

-- The zero function has zero Fourier integral; the character hypothesis
-- matters, as the integral is taken against `ψ`.
example {A : Type*} [CommRing A] [MeasurableSpace A] (ψ : AddChar A ℂ)
    (μ : Measure A) :
    fourierIntegral ψ μ 0 = 0 :=
  fourierIntegral_zero ψ μ

-- Pure tensors lie in the Schwartz--Bruhat space, with original binders.
example (F : Type*) [Field F] [NumberField F]
    {f : NumberField.AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    f ∈ schwartzBruhat F :=
  mem_schwartzBruhat_of_mem_pureTensorSet hf

-- The zero function lies in the Schwartz--Bruhat space.
example (F : Type*) [Field F] [NumberField F] :
    (0 : NumberField.AdeleRing (𝓞 F) F → ℂ) ∈ schwartzBruhat F :=
  zero_mem_schwartzBruhat

end NumberField.AdelicFourier
