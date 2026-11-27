/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.FormClassCorrespondence

open Complex PeriodPair BinaryQuadraticForm

/-- The number of homothety classes of proper ideals of the order of discriminant `D` is the
Gauss class number `h(D)`. -/
example {D : ℤ} (hD : ImaginaryQuadraticDiscriminant.IsImaginaryQuadraticDiscriminant D)
    {𝒪 : Subring ℂ}
    (h𝒪 : (𝒪 : Set ℂ) = {z | ∃ m n : ℤ, z = m + n * ((D + I * (Real.sqrt |(D : ℝ)| : ℂ)) / 2)}) :
    Nat.card (Quot (fun L L' : {L : PeriodPair // L.IsProperIdeal 𝒪} => L.1.IsHomothetic L'.1)) =
      MetaMathlibExt.gaussClassNumber D :=
  (formClasses_equiv_properIdealClasses hD h𝒪).2.2

/-- The lattice of the form `x² + y²` is a proper ideal of `ℤ[i]`, the order of discriminant
`-4`. -/
example {𝒪 : Subring ℂ}
    (h𝒪 : (𝒪 : Set ℂ) =
      {z | ∃ m n : ℤ, z = m + n * (((-4 : ℤ) + I * (Real.sqrt |((-4 : ℤ) : ℝ)| : ℂ)) / 2)})
    (L : PeriodPair) (h1 : L.ω₁ = (1 : ℤ))
    (h2 : L.ω₂ = (-((0 : ℤ) : ℂ) + I * (Real.sqrt |((-4 : ℤ) : ℝ)| : ℂ)) / 2) :
    L.IsProperIdeal 𝒪 :=
  (formClasses_equiv_properIdealClasses (D := -4) ⟨by norm_num, by norm_num⟩ h𝒪).1 (1, 0, 1) L
    (by norm_num) (by norm_num) (by norm_num [discrim]) h1 h2
