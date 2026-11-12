/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Market.TaxIncidence
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

open Filter Topology

/-! Tests for `MathlibExt.Economics.Market.TaxIncidence`: concrete instances with exact values. -/

namespace MathlibExtTest.Economics.Market.TaxIncidence

open _root_.MathlibExt.Economics.Market

-- Tests: concrete linear example `D p = 10 - p`, `S p = p`, path `p τ = 5 - τ / 2`.

/-- Seller-price rate `-1/2` in the linear example. -/
theorem test_sellerPrice : HasDerivAt (fun τ : ℝ => 5 - τ / 2) (-1/2 : ℝ) 0 := by
  have hpath : ∀ᶠ τ in 𝓝 (0:ℝ),
      IsBuyerTaxEquilibrium (fun p : ℝ => 10 - p) (fun p : ℝ => p) τ (5 - τ / 2) :=
    Filter.Eventually.of_forall (fun τ => by simp only [IsBuyerTaxEquilibrium]; ring)
  have hp : HasDerivAt (fun τ : ℝ => 5 - τ / 2) (-1/2 : ℝ) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (5:ℝ)).sub ((hasDerivAt_id' (0:ℝ)).div_const (2:ℝ))
    have hval : (0:ℝ) - 1 / 2 = -1 / 2 := by norm_num
    rw [hval] at h
    exact h
  have hD : HasDerivAt (fun p : ℝ => 10 - p) (-1 : ℝ) ((fun τ : ℝ => 5 - τ / 2) 0 + 0) := by
    have h : HasDerivAt (fun p : ℝ => 10 - p) (-1 : ℝ) 5 := by
      have h10 := (hasDerivAt_const (5:ℝ) (10:ℝ)).sub (hasDerivAt_id' (5:ℝ))
      have hval : (0:ℝ) - 1 = -1 := by norm_num
      rw [hval] at h10
      exact h10
    have hpt : (fun τ : ℝ => 5 - τ / 2) 0 + 0 = 5 := by norm_num
    rwa [hpt]
  have hS : HasDerivAt (fun p : ℝ => p) (1 : ℝ) ((fun τ : ℝ => 5 - τ / 2) 0) := by
    have hpt : (fun τ : ℝ => 5 - τ / 2) 0 = 5 := by norm_num
    rw [hpt]
    exact hasDerivAt_id' 5
  have hslope : (1:ℝ) ≠ -1 := by norm_num
  have h := hasDerivAt_sellerPrice (D := fun p : ℝ => 10 - p) (S := fun p : ℝ => p)
    (p := fun τ : ℝ => 5 - τ / 2) (τ₀ := (0:ℝ)) (D' := (-1:ℝ)) (S' := (1:ℝ)) (p' := (-1/2:ℝ))
    hpath hp hD hS hslope
  have hval : (-1:ℝ) / (1 - (-1)) = -1/2 := by norm_num
  rwa [hval] at h

/-- Buyer-price rate `1/2` in the linear example. -/
theorem test_buyerPrice : HasDerivAt (fun τ : ℝ => (5 - τ / 2) + τ) (1/2 : ℝ) 0 := by
  have hpath : ∀ᶠ τ in 𝓝 (0:ℝ),
      IsBuyerTaxEquilibrium (fun p : ℝ => 10 - p) (fun p : ℝ => p) τ (5 - τ / 2) :=
    Filter.Eventually.of_forall (fun τ => by simp only [IsBuyerTaxEquilibrium]; ring)
  have hp : HasDerivAt (fun τ : ℝ => 5 - τ / 2) (-1/2 : ℝ) 0 := by
    have h := (hasDerivAt_const (0:ℝ) (5:ℝ)).sub ((hasDerivAt_id' (0:ℝ)).div_const (2:ℝ))
    have hval : (0:ℝ) - 1 / 2 = -1 / 2 := by norm_num
    rw [hval] at h
    exact h
  have hD : HasDerivAt (fun p : ℝ => 10 - p) (-1 : ℝ) ((fun τ : ℝ => 5 - τ / 2) 0 + 0) := by
    have h : HasDerivAt (fun p : ℝ => 10 - p) (-1 : ℝ) 5 := by
      have h10 := (hasDerivAt_const (5:ℝ) (10:ℝ)).sub (hasDerivAt_id' (5:ℝ))
      have hval : (0:ℝ) - 1 = -1 := by norm_num
      rw [hval] at h10
      exact h10
    have hpt : (fun τ : ℝ => 5 - τ / 2) 0 + 0 = 5 := by norm_num
    rwa [hpt]
  have hS : HasDerivAt (fun p : ℝ => p) (1 : ℝ) ((fun τ : ℝ => 5 - τ / 2) 0) := by
    have hpt : (fun τ : ℝ => 5 - τ / 2) 0 = 5 := by norm_num
    rw [hpt]
    exact hasDerivAt_id' 5
  have hslope : (1:ℝ) ≠ -1 := by norm_num
  have h := hasDerivAt_buyerPrice (D := fun p : ℝ => 10 - p) (S := fun p : ℝ => p)
    (p := fun τ : ℝ => 5 - τ / 2) (τ₀ := (0:ℝ)) (D' := (-1:ℝ)) (S' := (1:ℝ)) (p' := (-1/2:ℝ))
    hpath hp hD hS hslope
  have hval : (1:ℝ) / (1 - (-1)) = 1/2 := by norm_num
  rwa [hval] at h

/-- Buyers' share `1/2` in the linear example. -/
theorem test_buyerShare : (1:ℝ) / (1 - (-1)) ∈ Set.Icc (0:ℝ) 1 :=
  buyerShare_mem_Icc (D' := (-1:ℝ)) (S' := (1:ℝ)) (by norm_num) (by norm_num) (by norm_num)

/-- Buyers' share value `1/2` in the linear example. -/
theorem test_buyerShare_value : (1:ℝ) / (1 - (-1)) = 1/2 := by norm_num

end MathlibExtTest.Economics.Market.TaxIncidence
