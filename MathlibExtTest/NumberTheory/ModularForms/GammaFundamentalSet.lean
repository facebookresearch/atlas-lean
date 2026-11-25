/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.GammaFundamentalSet

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Modular

/-- The unfolded integral, with the original binders. -/
theorem exactSource {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex]
    (hΓ : (-1 : SL(2, ℤ)) ∈ Γ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℍ → E)
    (hf : IntegrableOn f (gammaFundamentalSet Γ)) :
    ∫ τ in gammaFundamentalSet Γ, f τ =
      ∑ᶠ q : SL(2, ℤ) ⧸ Γ, ∫ τ in ModularGroup.fd,
        f ((Quotient.out q)⁻¹ • τ) :=
  integral_gammaFundamentalSet_eq_finsum_integral_fd hΓ f hf

/-- For the full group, the fundamental set is a single translate of `𝒟`,
and the unfolding collapses to one term: the `-1` hypothesis matters
because `-1` acts trivially on `ℍ`, so if `-1 ∉ Γ` then `a` and `-a`
represent distinct cosets whose tiles coincide, overlapping on the
whole positive-measure tile rather than only on the null boundary.
Requiring `-1 ∈ Γ` identifies those two cosets, so the tiles are
almost-everywhere disjoint. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℍ → E) (hf : IntegrableOn f (gammaFundamentalSet ⊤)) :
    ∫ τ in gammaFundamentalSet ⊤, f τ =
      ∑ᶠ q : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ)),
        ∫ τ in ModularGroup.fd, f ((Quotient.out q)⁻¹ • τ) :=
  integral_gammaFundamentalSet_eq_finsum_integral_fd (Subgroup.mem_top _) f hf
