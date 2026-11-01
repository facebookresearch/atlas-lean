/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.AbsNormSummable

open NumberField IsDedekindDomain

universe u

section

variable (F : Type u) [Field F] [NumberField F]

/-- The public `Infinite` instance accepts number fields in any universe. -/
example : Infinite (𝓞 F) := inferInstance

/-- The summability theorem accepts number fields in any universe. -/
example {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt F hσ

end

/-- For `σ > 1`, the Dedekind zeta terms over the primes of `ℤ` are
summable. -/
example {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 ℚ) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) :=
  NumberField.summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt ℚ hσ
