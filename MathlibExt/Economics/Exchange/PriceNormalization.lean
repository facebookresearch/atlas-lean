/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.DemandHomogeneity
public import MathlibExt.Economics.FirstWelfare

@[expose] public section

/-!
# Positive rescaling of equilibrium prices (Atlas EC15.T03)

Source: J. Levin, *General Equilibrium*, Stanford Econ 202 lecture notes (2006), §2.1
(consumer `i` maximizes `uⁱ` on `{x ∈ ℝ^L_+ : p · x ≤ p · eⁱ}`, prices `p ∈ ℝ^L_+`), Definition 1
(Walrasian equilibrium) and §6.2 ("Because `z(·)` is homogenous of degree zero, we can safely
normalize" prices). The scaling step is J. Levin, *Consumer Theory*, Proposition 3
(`x(λp, λw) = x(p, w)` for `λ > 0`), Atlas gap EC02.T03
`Economics.Consumer.isMarshallianDemand_smul_iff`. The equilibrium notion is the canonical
`ExchangeEconomy.IsWalrasianEquilibrium` of EC15.T02 (`MathlibExt.Economics.FirstWelfare`).
With wealth `p · eⁱ`, scaling `p` by `t > 0` scales wealth by `t`, so every consumer's demand is
unchanged; so are nonnegativity of prices, `p ≠ 0`, feasibility and the set of positive-price
goods whose markets must clear. Hence the set of equilibrium allocations is unchanged.
-/

namespace MathlibExt.Economics.ExchangeEconomy

/-- Rescaling prices by a positive factor preserves Walrasian equilibrium with the same
allocation. -/
theorem isWalrasianEquilibrium_smul_iff {I L : Type*} [Fintype I] [Fintype L]
    (E : ExchangeEconomy I L) {t : ℝ} (ht : 0 < t) (p : L → ℝ) (x : I → L → ℝ) :
    E.IsWalrasianEquilibrium (t • p) x ↔ E.IsWalrasianEquilibrium p x := by
  have hnonneg : (0 : L → ℝ) ≤ t • p ↔ (0 : L → ℝ) ≤ p := by
    simp only [Pi.le_def, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact forall_congr' fun l => mul_nonneg_iff_of_pos_left ht
  have hne : t • p ≠ 0 ↔ p ≠ 0 := by
    rw [ne_eq, ne_eq, smul_eq_zero]
    simp [ht.ne']
  have hpos : ∀ l, 0 < (t • p) l ↔ 0 < p l := by
    intro l
    rw [Pi.smul_apply, smul_eq_mul]
    exact mul_pos_iff_of_pos_left ht
  have hdot : ∀ i, (t • p) ⬝ᵥ E.endowment i = t * (p ⬝ᵥ E.endowment i) := by
    intro i
    rw [smul_dotProduct, smul_eq_mul]
  have hdem : ∀ i, _root_.Economics.Consumer.IsMarshallianDemand (E.utility i) {z | 0 ≤ z}
        (t • p) ((t • p) ⬝ᵥ E.endowment i) (x i) ↔
      _root_.Economics.Consumer.IsMarshallianDemand (E.utility i) {z | 0 ≤ z}
        p (p ⬝ᵥ E.endowment i) (x i) := by
    intro i
    rw [hdot i]
    exact _root_.Economics.Consumer.isMarshallianDemand_smul_iff _ _ ht _ _ _
  simp only [IsWalrasianEquilibrium, hnonneg, hne, hpos, hdem]

end MathlibExt.Economics.ExchangeEconomy
