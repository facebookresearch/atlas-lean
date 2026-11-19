/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.SupplyDemand
public import Mathlib.Basic.Real.Basic

/-!
# Buyer-tax and seller-tax equivalence

A per-unit tax `τ` drives a wedge between the price buyers pay and the price sellers receive.
Levied on buyers, an equilibrium seller price `p` solves `D (p + τ) = S p`; levied on sellers,
an equilibrium buyer price `p` solves `D p = S (p - τ)`. The two formulations correspond under
`p ↦ p + τ`: the same buyer price, seller price and traded quantity, whoever remits the tax.
With no tax both are ordinary equilibria.

## Main results

* `MathlibExt.Economics.Market.isBuyerTaxEquilibrium_iff_isSellerTaxEquilibrium_add`
* `MathlibExt.Economics.Market.image_add_setOf_isBuyerTaxEquilibrium`

## References

* H. R. Varian, *Intermediate Microeconomics*, Norton, Chapter 16 (taxes).

Atlas roadmap target EC08.T02.
-/

@[expose] public section

namespace MathlibExt.Economics.Market

/-- Equilibrium when the tax `τ` is levied on buyers: `p` is the market price sellers receive,
buyers pay `p + τ`. -/
def IsBuyerTaxEquilibrium (D S : ℝ → ℝ) (τ p : ℝ) : Prop :=
  D (p + τ) = S p

/-- Equilibrium when the tax `τ` is levied on sellers: `p` is the market price buyers pay,
sellers receive `p - τ`. -/
def IsSellerTaxEquilibrium (D S : ℝ → ℝ) (τ p : ℝ) : Prop :=
  D p = S (p - τ)

/-- A buyer-tax equilibrium with seller price `p` is a seller-tax equilibrium with buyer price
`p + τ`, and conversely: both have the same buyer price, seller price and traded quantity. -/
theorem isBuyerTaxEquilibrium_iff_isSellerTaxEquilibrium_add {D S : ℝ → ℝ} {τ p : ℝ} :
    IsBuyerTaxEquilibrium D S τ p ↔ IsSellerTaxEquilibrium D S τ (p + τ) := by
  unfold IsBuyerTaxEquilibrium IsSellerTaxEquilibrium
  rw [add_sub_cancel_right]

/-- A seller-tax equilibrium with buyer price `p` is a buyer-tax equilibrium with seller price
`p - τ`, and conversely. -/
theorem isSellerTaxEquilibrium_iff_isBuyerTaxEquilibrium_sub {D S : ℝ → ℝ} {τ p : ℝ} :
    IsSellerTaxEquilibrium D S τ p ↔ IsBuyerTaxEquilibrium D S τ (p - τ) := by
  unfold IsSellerTaxEquilibrium IsBuyerTaxEquilibrium
  rw [sub_add_cancel]

/-- **Tax equivalence.** Shifting by the wedge maps the buyer-tax equilibrium prices onto the
seller-tax equilibrium prices. -/
theorem image_add_setOf_isBuyerTaxEquilibrium (D S : ℝ → ℝ) (τ : ℝ) :
    (fun p => p + τ) '' {p | IsBuyerTaxEquilibrium D S τ p} =
      {p | IsSellerTaxEquilibrium D S τ p} := by
  ext q
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact isBuyerTaxEquilibrium_iff_isSellerTaxEquilibrium_add.mp hp
  · intro hq
    exact ⟨q - τ, isSellerTaxEquilibrium_iff_isBuyerTaxEquilibrium_sub.mp hq, sub_add_cancel q τ⟩

/-- With no tax, a buyer-tax equilibrium is an ordinary equilibrium. -/
theorem isBuyerTaxEquilibrium_zero_iff {D S : ℝ → ℝ} {p : ℝ} :
    IsBuyerTaxEquilibrium D S 0 p ↔ IsEquilibrium D S p := by
  unfold IsBuyerTaxEquilibrium IsEquilibrium
  rw [add_zero]

/-- With no tax, a seller-tax equilibrium is an ordinary equilibrium. -/
theorem isSellerTaxEquilibrium_zero_iff {D S : ℝ → ℝ} {p : ℝ} :
    IsSellerTaxEquilibrium D S 0 p ↔ IsEquilibrium D S p := by
  unfold IsSellerTaxEquilibrium IsEquilibrium
  rw [sub_zero]

end MathlibExt.Economics.Market
