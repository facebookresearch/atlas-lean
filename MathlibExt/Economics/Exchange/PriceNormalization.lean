/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.DemandHomogeneity
public import MathlibExt.Economics.SecondWelfareTheorem
public import MathlibExt.Economics.FirstWelfare

@[expose] public section

/-!
# Positive rescaling of equilibrium prices (Atlas EC15.T03)

Source: J. Levin, *General Equilibrium*, Stanford Econ 202 lecture notes (2006), §2.1
(consumer `i` maximizes `uⁱ` on `{x ∈ ℝ^L_+ : p · x ≤ p · eⁱ}`, prices `p ∈ ℝ^L_+`), Definition 1
(Walrasian equilibrium) and §6.2 ("Because `z(·)` is homogenous of degree zero, we can safely
normalize" prices). The scaling step is J. Levin, *Consumer Theory*, Proposition 3
(`x(λp, λw) = x(p, w)` for `λ > 0`), Atlas gap EC02.T03
`Economics.Consumer.isMarshallianDemand_smul_iff`. With wealth `p · eⁱ`, scaling `p` by
`t > 0` scales
wealth by `t`, so every consumer's demand, and hence the set of equilibrium allocations, is
unchanged. The demand predicate is the canonical `Economics.Consumer` one (EC02.T03 as merged
in #1443), not the `TwoGood` duplicate of the same shape. This predicate is Levin's
(Definition 1): exact market clearing and nonnegative endowments, with `p = 0`
allowed in the statement (the tests show no equilibrium exists there). It is
deliberately distinct from `ExchangeEconomy.IsWalrasianEquilibrium`
(EC15.T02, Mas-Colell–Whinston–Green Definition 16.B), which instead requires
`p ≠ 0`, free disposal (`∑ x ≤ ∑ e`), and clearing only at positive-price
goods; neither predicate implies the other. The bridge theorem below connects
them: a Levin equilibrium at nonzero prices is an MWG equilibrium.
-/

namespace MathlibExt.Economics.Exchange

/-- `(p, x)` is a Walrasian equilibrium of the exchange economy with utilities `u` and
endowments `e` (Levin, *General Equilibrium*, §2.1 and Definition 1): endowments lie in `ℝ^L_+`,
prices are nonnegative, each `x i` is a Marshallian demand of consumer `i` on `ℝ^L_+` at prices
`p` and wealth `p · e i`, and markets clear, `∑ i, x i = ∑ i, e i`. -/
def IsLevinWalrasianEquilibrium {I L : Type*} [Fintype I] [Fintype L] (u : I → (L → ℝ) → ℝ)
    (e : I → L → ℝ) (p : L → ℝ) (x : I → L → ℝ) : Prop :=
  (∀ i, e i ∈ SecondWelfareTheorem.consumptionSet L) ∧ 0 ≤ p ∧
    (∀ i, Economics.Consumer.IsMarshallianDemand (u i) (SecondWelfareTheorem.consumptionSet L) p
      (p ⬝ᵥ e i) (x i)) ∧
    ∑ i, x i = ∑ i, e i

/-- Rescaling prices by a positive factor preserves Walrasian equilibrium with the same
allocation. -/
theorem isLevinWalrasianEquilibrium_smul_iff {I L : Type*} [Fintype I] [Fintype L]
    (u : I → (L → ℝ) → ℝ) (e : I → L → ℝ) {t : ℝ} (ht : 0 < t) (p : L → ℝ) (x : I → L → ℝ) :
    IsLevinWalrasianEquilibrium u e (t • p) x ↔ IsLevinWalrasianEquilibrium u e p x := by
  have hnonneg : (0 : L → ℝ) ≤ t • p ↔ (0 : L → ℝ) ≤ p := by
    simp only [Pi.le_def, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact forall_congr' fun l => mul_nonneg_iff_of_pos_left ht
  have hdot : ∀ i, (t • p) ⬝ᵥ e i = t * (p ⬝ᵥ e i) := by
    intro i
    rw [smul_dotProduct, smul_eq_mul]
  have hdem : ∀ i, Economics.Consumer.IsMarshallianDemand (u i)
      (SecondWelfareTheorem.consumptionSet L) (t • p) ((t • p) ⬝ᵥ e i) (x i) ↔
      Economics.Consumer.IsMarshallianDemand (u i)
        (SecondWelfareTheorem.consumptionSet L) p (p ⬝ᵥ e i) (x i) := by
    intro i
    rw [hdot i]
    exact Economics.Consumer.isMarshallianDemand_smul_iff _ _ ht _ _ _
  simp only [IsLevinWalrasianEquilibrium, hnonneg, hdem]


/-- Bridge: a Levin equilibrium at nonzero prices is an MWG equilibrium
(`ExchangeEconomy.IsWalrasianEquilibrium`) for the economy with the same
endowments and utilities. Feasibility of the allocation and clearing at
positive-price goods follow from exact clearing and the demand condition
(demanded bundles lie in the consumption set). -/
theorem isWalrasianEquilibrium_of_isLevinWalrasianEquilibrium
    {I L : Type*} [Fintype I] [Fintype L]
    (u : I → (L → ℝ) → ℝ) (e : I → L → ℝ) {p : L → ℝ} {x : I → L → ℝ}
    (hpne : p ≠ 0) (h : IsLevinWalrasianEquilibrium u e p x) :
    ExchangeEconomy.IsWalrasianEquilibrium ⟨e, u⟩ p x := by
  obtain ⟨he, hp, hdem, hclear⟩ := h
  have hset : SecondWelfareTheorem.consumptionSet L = {z : L → ℝ | 0 ≤ z} := by
    ext z
    simp only [SecondWelfareTheorem.consumptionSet, Set.mem_ofPred_eq, Pi.le_def,
      Pi.zero_apply]
  refine ⟨hp, hpne, ⟨?hfeas, ?hfree⟩, ?hclearpos, ?hdem⟩
  · intro i
    exact (hdem i).1.1
  · rw [hclear]
  · intro l hl
    exact congrFun hclear l
  · intro i
    rw [← hset]
    exact hdem i

end MathlibExt.Economics.Exchange
