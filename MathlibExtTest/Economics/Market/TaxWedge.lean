/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.TaxWedge
public import Mathlib.Tactic.NormNum.Basic

@[expose] public section

/-! Tests for `MathlibExt.Economics.Market.TaxWedge`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Market.TaxWedge

open _root_.Economics.Market

/-! ## Tests: concrete values D p = 10 - p, S p = p, τ = 2 -/

/-- Test: buyer-tax equilibrium at seller price 4. -/
theorem test_buyer_4 :
    IsBuyerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 4 := by
  unfold IsBuyerTaxEquilibrium
  norm_num

/-- Test: seller-tax equilibrium at buyer price 6. -/
theorem test_seller_6 :
    IsSellerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 6 := by
  unfold IsSellerTaxEquilibrium
  norm_num

/-- Test: derive the seller-tax equilibrium (buyer price 6) from the buyer-tax one. -/
theorem test_buyer_to_seller :
    IsSellerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 6 := by
  have h := isBuyerTaxEquilibrium_iff_isSellerTaxEquilibrium_add.mp test_buyer_4
  have e : (4 : ℝ) + 2 = 6 := by norm_num
  rw [e] at h
  exact h

/-- Test: derive the buyer-tax equilibrium (seller price 4) from the seller-tax one. -/
theorem test_seller_to_buyer :
    IsBuyerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 4 := by
  have h := isSellerTaxEquilibrium_iff_isBuyerTaxEquilibrium_sub.mp test_seller_6
  have e : (6 : ℝ) - 2 = 4 := by norm_num
  rw [e] at h
  exact h

/-- Test: traded quantity is 4 (demand at buyer price 6, supply at seller price 4). -/
theorem test_quantity :
    (fun p : ℝ => 10 - p) 6 = 4 ∧ (fun p : ℝ => p) 4 = 4 := by
  constructor <;> norm_num

/-- Test: with no tax, buyer-tax equilibrium at price 5 is an ordinary equilibrium. -/
theorem test_zero_buyer_eq :
    IsEquilibrium (fun p => 10 - p) (fun p => p) 5 := by
  have h : IsBuyerTaxEquilibrium (fun p => 10 - p) (fun p => p) 0 5 := by
    unfold IsBuyerTaxEquilibrium
    norm_num
  exact isBuyerTaxEquilibrium_zero_iff.mp h

/-- Test: derive seller-tax membership (buyer price 6) from buyer-tax membership (seller
price 4) through the image equality. -/
theorem test_image_mem :
    (6 : ℝ) ∈ {p | IsSellerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 p} := by
  have him := image_add_setOf_isBuyerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2
  have h4 : (4 : ℝ) ∈ {p | IsBuyerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 p} :=
    test_buyer_4
  have himg : (4 : ℝ) + 2 ∈ (fun p => p + 2) '' {p | IsBuyerTaxEquilibrium (fun p => 10 - p) (fun p => p) 2 p} :=
    Set.mem_image_of_mem (fun p => p + 2) h4
  rw [him] at himg
  have e : (4 : ℝ) + 2 = 6 := by norm_num
  rw [e] at himg
  exact himg

/-- Test: with no tax, seller-tax equilibrium at price 5 is an ordinary equilibrium. -/
theorem test_zero_seller_eq :
    IsEquilibrium (fun p => 10 - p) (fun p => p) 5 := by
  have h : IsSellerTaxEquilibrium (fun p => 10 - p) (fun p => p) 0 5 := by
    unfold IsSellerTaxEquilibrium
    norm_num
  exact isSellerTaxEquilibrium_zero_iff.mp h

end MathlibExtTest.Economics.Market.TaxWedge
