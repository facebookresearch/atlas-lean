/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.TaxWedge
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Tax incidence from supply and demand slopes

Along an equilibrium path `τ ↦ p τ` (seller price) of a unit tax levied on buyers,
`D (p τ + τ) = S (p τ)` near `τ₀`. If the path is differentiable at `τ₀` (assumed here, not
derived) and `D`, `S` have slopes `D'`, `S'` with `S' ≠ D'`, the seller price moves at rate
`D' / (S' - D')` and the buyer price at rate `S' / (S' - D')`. With downward-sloping demand and
upward-sloping supply the buyers' share of a small tax lies in `[0, 1]`.

## Main results

* `MathlibExt.Economics.Market.hasDerivAt_sellerPrice`
* `MathlibExt.Economics.Market.hasDerivAt_buyerPrice`
* `MathlibExt.Economics.Market.buyerShare_mem_Icc`

## References

* H. R. Varian, *Intermediate Microeconomics*, Norton, Chapter 16 (taxes).

Atlas roadmap target EC08.T03.
-/

@[expose] public section

open Filter Topology

namespace MathlibExt.Economics.Market

/-- **Seller-price incidence.** Along a differentiable equilibrium path, the seller price moves
at rate `D' / (S' - D')` in the tax. -/
theorem hasDerivAt_sellerPrice {D S p : ℝ → ℝ} {τ₀ D' S' p' : ℝ}
    (hpath : ∀ᶠ τ in 𝓝 τ₀, IsBuyerTaxEquilibrium D S τ (p τ)) (hp : HasDerivAt p p' τ₀)
    (hD : HasDerivAt D D' (p τ₀ + τ₀)) (hS : HasDerivAt S S' (p τ₀)) (hslope : S' ≠ D') :
    HasDerivAt p (D' / (S' - D')) τ₀ := by
  have hInner : HasDerivAt (fun τ => p τ + τ) (p' + 1) τ₀ :=
    hp.add (hasDerivAt_id' τ₀)
  have hleft : HasDerivAt (D ∘ fun τ => p τ + τ) (D' * (p' + 1)) τ₀ :=
    HasDerivAt.comp (h := fun τ => p τ + τ) τ₀ hD hInner
  have hright : HasDerivAt (S ∘ p) (S' * p') τ₀ := hS.comp τ₀ hp
  have heq : (D ∘ fun τ => p τ + τ) =ᶠ[𝓝 τ₀] (S ∘ p) := hpath
  have huniq : D' * (p' + 1) = S' * p' :=
    (hleft.congr_of_eventuallyEq heq.symm).unique hright
  have hne : S' - D' ≠ 0 := sub_ne_zero.mpr hslope
  have hval : p' = D' / (S' - D') := by
    rw [eq_div_iff hne]
    linear_combination -huniq
  rwa [hval] at hp

/-- **Buyer-price incidence.** Along a differentiable equilibrium path, the buyer price
`p τ + τ` moves at rate `S' / (S' - D')` in the tax. -/
theorem hasDerivAt_buyerPrice {D S p : ℝ → ℝ} {τ₀ D' S' p' : ℝ}
    (hpath : ∀ᶠ τ in 𝓝 τ₀, IsBuyerTaxEquilibrium D S τ (p τ)) (hp : HasDerivAt p p' τ₀)
    (hD : HasDerivAt D D' (p τ₀ + τ₀)) (hS : HasDerivAt S S' (p τ₀)) (hslope : S' ≠ D') :
    HasDerivAt (fun τ => p τ + τ) (S' / (S' - D')) τ₀ := by
  have hSeller : HasDerivAt p (D' / (S' - D')) τ₀ :=
    hasDerivAt_sellerPrice hpath hp hD hS hslope
  have hAdd := hSeller.add (hasDerivAt_id' τ₀)
  have hne : S' - D' ≠ 0 := sub_ne_zero.mpr hslope
  have halg : D' / (S' - D') + 1 = S' / (S' - D') := by
    field_simp
    ring
  rw [halg] at hAdd
  exact hAdd

/-- With downward-sloping demand and upward-sloping supply, the buyers' share
`S' / (S' - D')` of a small tax lies in `[0, 1]`. -/
theorem buyerShare_mem_Icc {D' S' : ℝ} (hD' : D' ≤ 0) (hS' : 0 ≤ S') (hslope : S' ≠ D') :
    S' / (S' - D') ∈ Set.Icc (0 : ℝ) 1 := by
  have hlt : D' < S' := lt_of_le_of_ne (le_trans hD' hS') (Ne.symm hslope)
  have hpos : 0 < S' - D' := sub_pos.mpr hlt
  rw [Set.mem_Icc]
  refine ⟨div_nonneg hS' (le_of_lt hpos), ?_⟩
  rw [div_le_one hpos]
  linarith

end MathlibExt.Economics.Market
