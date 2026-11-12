/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.DemandHomogeneity
public import MathlibExt.Economics.Consumer.MarshallianDemand
public import MathlibExt.Economics.SecondWelfareTheorem

@[expose] public section

/-!
# Positive rescaling of equilibrium prices (Atlas EC15.T03)

Source: J. Levin, *General Equilibrium*, Stanford Econ 202 lecture notes (2006), §2.1
(consumer `i` maximizes `uⁱ` on `{x ∈ ℝ^L_+ : p · x ≤ p · eⁱ}`, prices `p ∈ ℝ^L_+`), Definition 1
(Walrasian equilibrium) and §6.2 ("Because `z(·)` is homogenous of degree zero, we can safely
normalize" prices). The scaling step is J. Levin, *Consumer Theory*, Proposition 3
(`x(λp, λw) = x(p, w)` for `λ > 0`), Atlas gap EC02.T03
`Consumer.isMarshallianDemand_smul_iff`. With wealth `p · eⁱ`, scaling `p` by `t > 0` scales
wealth by `t`, so every consumer's demand, and hence the set of equilibrium allocations, is
unchanged.
-/

namespace MathlibExt.Economics.Exchange

/-- `(p, x)` is a Walrasian equilibrium of the exchange economy with utilities `u` and
endowments `e` (Levin, *General Equilibrium*, §2.1 and Definition 1): endowments lie in `ℝ^L_+`,
prices are nonnegative and nonzero, each `x i` is a Marshallian demand of consumer `i` at
prices `p` and wealth `p · e i` (against the canonical EC02.T01 `marshallianDemand`), and
markets clear, `∑ i, x i = ∑ i, e i`. The `p ≠ 0` requirement excludes the degenerate
zero-price case: with constant utility and zero endowments every other conjunct holds at
`p = 0`, but such a price cannot be normalized. -/
def IsWalrasianEquilibrium {I L : Type*} [Fintype I] [Fintype L] (u : I → (L → ℝ) → ℝ)
    (e : I → L → ℝ) (p : L → ℝ) (x : I → L → ℝ) : Prop :=
  (∀ i, e i ∈ SecondWelfareTheorem.consumptionSet L) ∧ 0 ≤ p ∧ p ≠ 0 ∧
    (∀ i, x i ∈ Consumer.marshallianDemand (u i) p (p ⬝ᵥ e i)) ∧
    ∑ i, x i = ∑ i, e i

/-- Rescaling prices by a positive factor preserves Walrasian equilibrium with the same
allocation. -/
theorem isWalrasianEquilibrium_smul_iff {I L : Type*} [Fintype I] [Fintype L]
    (u : I → (L → ℝ) → ℝ) (e : I → L → ℝ) {t : ℝ} (ht : 0 < t) (p : L → ℝ) (x : I → L → ℝ) :
    IsWalrasianEquilibrium u e (t • p) x ↔ IsWalrasianEquilibrium u e p x := by
  have hnonneg : (0 : L → ℝ) ≤ t • p ↔ (0 : L → ℝ) ≤ p := by
    simp only [Pi.le_def, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
    exact forall_congr' fun l => mul_nonneg_iff_of_pos_left ht
  have hne : t • p ≠ 0 ↔ p ≠ 0 := by
    rw [ne_eq, ne_eq, smul_eq_zero]
    simp [ht.ne']
  have hdot : ∀ i, (t • p) ⬝ᵥ e i = t * (p ⬝ᵥ e i) := by
    intro i
    rw [smul_dotProduct, smul_eq_mul]
  have hdem : ∀ i, x i ∈ Consumer.marshallianDemand (u i) (t • p) ((t • p) ⬝ᵥ e i) ↔
      x i ∈ Consumer.marshallianDemand (u i) p (p ⬝ᵥ e i) := by
    intro i
    rw [hdot i]
    exact Consumer.isMarshallianDemand_smul_iff _ ht _ _ _
  simp only [IsWalrasianEquilibrium, hnonneg, hne, hdem]

end MathlibExt.Economics.Exchange
