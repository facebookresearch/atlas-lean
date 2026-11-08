/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.FieldTheory.EssentialDimensionSymmetric

@[expose] public section

namespace MathlibExt.FieldTheory.EssentialDimensionSymmetricWanted

open MathlibExt.FieldTheory.EssentialDimensionSymmetric

/-!
# Catalogue bounds for the essential dimension of symmetric groups

The frozen catalogue bounds for `C₇₉ = lim sup (ed_ℂ(Sₙ) / n)` as proof
requests against `edSn` and `essDimRatio`, the descent parameter count
of the general polynomial `Xⁿ - a₁Xⁿ⁻¹ + ⋯ + (-1)ⁿaₙ` formalized in the
provider.

Scope: the catalogue defines `ed_ℂ(Sₙ)` as this Tschirnhaus parameter
count, noting Buhler--Reichstein's theorem that it equals the essential
dimension. The formalization covers the general-polynomial formulation
only: arbitrary `Sₙ`-torsors, versal torsors, and the
Buhler--Reichstein equivalence are not formalized. The elementary bound
`edSn n ≤ n`, hence `C₇₉ ≤ 1`, is proved in the provider; the sharper
bounds below are recorded as proof requests.
-/

/-- Source: Buhler--Reichstein (1997), the classical Tschirnhaus bound
`ed_ℂ(Sₙ) ≤ n - 3` for `n ≥ 5`. -/
theorem_wanted buhlerReichstein1997UpperBound_wanted :
    ∀ n ≥ 5, edSn n ≤ n - 3

/-- Source: Buhler--Reichstein (1997) and Duncan, the lower bound
`⌊n/2⌋ ≤ ed_ℂ(Sₙ)`. -/
theorem_wanted buhlerReichsteinDuncanLowerBound_wanted :
    ∀ n : ℕ, n / 2 ≤ edSn n

/-- Source: catalogue lower row for `C₇₉`, from the `⌊n/2⌋` lower
bound: `1/2 ≤ C₇₉`. -/
theorem_wanted essDimRatioLowerBound_wanted :
    (1 / 2 : ℝ) ≤ essDimRatio

/-- Source: Buhler--Reichstein (1997), exact value `ed_ℂ(S₅) = 2`: their
general bounds `⌊5/2⌋ ≤ ed_ℂ(S₅) ≤ 5 - 3` coincide at `2`. The classical
Bring--Jerrard form `X^5 + pX + q` is not the descent behind that upper
bound here: producing it already requires solving auxiliary equations
over an extension of the coefficient field, and normalizing further to
`X^5 + X + a` is again only a scaling over an extension, so neither form
witnesses a descent over the original field in the sense of this file
(in particular nothing here implies `edSn 5 ≤ 1`). -/
theorem_wanted edSn_five_wanted : edSn 5 = 2

/-- Source: Buhler--Reichstein (1997), exact value `ed_ℂ(S₄) = 2`. -/
theorem_wanted edSn_four_wanted : edSn 4 = 2

/-- Source: Buhler--Reichstein (1997), exact value `ed_ℂ(S₆) = 3`. -/
theorem_wanted edSn_six_wanted : edSn 6 = 3

/-- Source: Duncan (2010), *Essential dimensions of `A₇` and `S₇`*,
exact value `ed_ℂ(S₇) = 4`. Buhler--Reichstein's general bounds give
only `3 ≤ ed_ℂ(S₇) ≤ 4` here. -/
theorem_wanted edSn_seven_wanted : edSn 7 = 4

end MathlibExt.FieldTheory.EssentialDimensionSymmetricWanted
