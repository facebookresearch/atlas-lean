/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic

/-!
# Ideal multiplicity is unchanged under localization at a maximal ideal

For a Dedekind domain `R` and a maximal ideal `p`, the exponent of `p` in an
ideal `I` (as recorded by `emultiplicity`) agrees with the exponent of the
maximal ideal of any localization `Rₚ` at `p` in the mapped ideal `I.map`.

This invariant is the first corrected prerequisite for ATLAS `NumberTheoryI`
N261: the helper `different_valuation_exact` (claiming
`d_P = e_P - 1 + v_P(e_P)`) is false in wildly ramified extensions, so N261
will formalize only the true two-sided bound. Transporting valuations of
`differentIdeal A B` and of the correction term `Ideal.span {(e : B)}` to the
localization at a prime is the step that makes the local computation available.

## Main result

- `IsLocalization.AtPrime.emultiplicity_maximalIdeal_map_eq`: the exponent of
  an ideal at a maximal ideal equals the exponent of its image at the maximal
  ideal of the localization.
-/

@[expose] public section

namespace IsLocalization.AtPrime

/-- **Ideal multiplicity is unchanged by localization at a maximal ideal.** Let $R$ be a
Dedekind domain, $\mathfrak p$ a maximal ideal of $R$, and $R_{\mathfrak p}$ a local ring that
is a localization of $R$ at $\mathfrak p$, with maximal ideal $\mathfrak m$. Then for every
ideal $I$ of $R$, the multiplicity of $\mathfrak m$ in the extended ideal $I R_{\mathfrak p}$
equals the multiplicity of $\mathfrak p$ in $I$. Here the multiplicity of an ideal $J$ in an
ideal $K$ is the largest $n$ with $J^n \mid K$, or $\infty$ if $J^n \mid K$ for every $n$. -/
theorem emultiplicity_maximalIdeal_map_eq
    {R Rₚ : Type*} [CommRing R] [IsDedekindDomain R]
    (p : Ideal R) [p.IsMaximal] [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (I : Ideal R) :
    emultiplicity (IsLocalRing.maximalIdeal Rₚ)
        (I.map (algebraMap R Rₚ)) =
      emultiplicity p I := by
  have : IsDomain Rₚ := IsLocalization.isDomain_of_atPrime Rₚ p
  have : IsDedekindDomain Rₚ :=
    IsLocalization.AtPrime.isDedekindDomain R p Rₚ
  rw [emultiplicity_eq_emultiplicity_iff]
  intro n
  rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le,
    Ideal.map_le_iff_le_comap, ← Ideal.under_def,
    IsLocalization.AtPrime.under_maximalIdeal_pow p Rₚ n]

end IsLocalization.AtPrime
