/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.MechanismDesign.VCG
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Max

open Finset MathlibExt.GameTheory.MechanismDesign.VCG

/-- A welfare-maximizing choice rule over three alternatives for two agents. -/
noncomputable def argmaxRule (v : Fin 2 → Fin 3 → ℝ) : Fin 3 :=
  Classical.choose (exists_max_image univ (welfare v) univ_nonempty)

theorem argmaxRule_spec (v : Fin 2 → Fin 3 → ℝ) (a : Fin 3) :
    welfare v a ≤ welfare v (argmaxRule v) :=
  (Classical.choose_spec (exists_max_image univ (welfare v) univ_nonempty)).2 a (mem_univ a)

/-- VCG with Clarke pivot payments over this rule is incentive compatible. -/
example : IsIncentiveCompatible argmaxRule (grovesPayment argmaxRule clarkePivot) :=
  isIncentiveCompatible_clarke argmaxRule_spec

/-- Clarke payments are nonnegative, and truthful agents with nonnegative values get a
nonnegative utility. -/
example (v : Fin 2 → Fin 3 → ℝ) (i : Fin 2) : 0 ≤ grovesPayment argmaxRule clarkePivot v i :=
  clarkePayment_nonneg argmaxRule v i

example (v : Fin 2 → Fin 3 → ℝ) (hv : ∀ i a, 0 ≤ v i a) (i : Fin 2) :
    0 ≤ v i (argmaxRule v) - grovesPayment argmaxRule clarkePivot v i :=
  clarke_utility_nonneg (argmaxRule_spec v) hv i

/-- Groves payments with the zero pivot term are incentive compatible too. -/
example : IsIncentiveCompatible argmaxRule (grovesPayment argmaxRule fun _ _ => 0) :=
  isIncentiveCompatible_groves argmaxRule_spec fun _ _ _ => rfl

/-- A highest-bid winner rule for three bidders. -/
noncomputable def highestBidder (t : Fin 3 → ℝ) : Fin 3 :=
  Classical.choose (exists_max_image univ t univ_nonempty)

theorem highestBidder_spec (t : Fin 3 → ℝ) (j : Fin 3) : t j ≤ t (highestBidder t) :=
  (Classical.choose_spec (exists_max_image univ t univ_nonempty)).2 j (mem_univ j)

/-- Vickrey's second-price auction is truthful for nonnegative bids. -/
example (t : Fin 3 → ℝ) (ht : ∀ j, 0 ≤ t j) (i : Fin 3) (s : ℝ) (hs : 0 ≤ s) :
    (if highestBidder (Function.update t i s) = i then t i else 0) -
        secondPricePayment highestBidder (Function.update t i s) i ≤
      (if highestBidder t = i then t i else 0) - secondPricePayment highestBidder t i :=
  secondPrice_truthful highestBidder_spec ht i hs

/-- It coincides with the VCG mechanism with Clarke pivot payments. -/
example (t : Fin 3 → ℝ) (ht : ∀ j, 0 ≤ t j) (i : Fin 3) :
    grovesPayment (fun v => highestBidder fun j => v j j) clarkePivot (singleItem t) i =
      secondPricePayment highestBidder t i :=
  grovesPayment_singleItem highestBidder_spec ht i

/-- Losers pay nothing. -/
example (t : Fin 3 → ℝ) (i : Fin 3) (h : highestBidder t ≠ i) :
    secondPricePayment highestBidder t i = 0 := by
  simp [secondPricePayment, h]
