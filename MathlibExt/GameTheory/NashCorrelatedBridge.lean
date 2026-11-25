/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.CorrelatedEquilibrium
public import MathlibExt.GameTheory.MixedNashExistence

@[expose] public section

/-! # Mixed Nash equilibria are correlated equilibria

`MathlibExt.GameTheory.MixedNashExistence` defines mixed Nash equilibria in payoff form and
proves Nash's theorem; `MathlibExt.GameTheory.CorrelatedEquilibrium` works in cost form and
proves that product distributions of mutual best responses are correlated equilibria
(`isCorrelatedEq_productDist`). This module connects the two definitions.

## References

* S. Hart and A. Mas-Colell, "A simple adaptive procedure leading to correlated equilibrium",
  Econometrica 68(5) (2000), 1127–1150, §2.
* S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §6.
-/

namespace MathlibExt.GameTheory.NashCorrelatedBridge

open Finset
open MathlibExt.GameTheory.CorrelatedEquilibrium (IsCorrelatedEq productDist othersWeight
  pureCost)

section NashBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

open MathlibExt.GameTheory.MixedNashExistence (IsMixedNash expectedPayoff)

/-- **Mixed Nash equilibria are correlated equilibria** (Hart and Mas-Colell 2000, §2; Hart
2005, §6): if `σ` is a mixed Nash equilibrium of the game with payoffs `u`
(`MixedNashExistence.IsMixedNash`), the product distribution `s ↦ ∏ᵢ σᵢ(sᵢ)` is a correlated
equilibrium of the game with costs `-u`. This bridges the payoff-form definition used for the
existence theorem of Nash with the cost form of `CorrelatedEquilibrium`, via
`CorrelatedEquilibrium.isCorrelatedEq_productDist`. -/
theorem isCorrelatedEq_productDist_of_isMixedNash {u : ι → (∀ i, S i) → ℝ}
    {σ : ∀ i, Convexity.StdSimplex ℝ (S i)} (h : IsMixedNash u σ) :
    IsCorrelatedEq (fun i s => -u i s) (productDist fun i => (σ i).weights) 0 := by
  have hsum : ∀ i (τ : Convexity.StdSimplex ℝ (S i)), ∑ a, τ.weights a = 1 := fun i τ => by
    rw [← Finsupp.sum_fintype τ.weights (fun _ r => r) (fun _ => rfl)]
    exact τ.total
  refine MathlibExt.GameTheory.CorrelatedEquilibrium.isCorrelatedEq_productDist
    (fun i a => (σ i).nonneg a) (fun i => hsum i (σ i)) fun i a => ?_
  have hdev := h i (Convexity.StdSimplex.single a)
  have hlhs : expectedPayoff u (Function.update σ i (Convexity.StdSimplex.single a)) i =
      -pureCost (fun i s => -u i s) (fun i => (σ i).weights) i a := by
    simp only [expectedPayoff, pureCost, ← sum_neg_distrib]
    refine sum_congr rfl fun s _ => ?_
    have hprod := MathlibExt.GameTheory.CorrelatedEquilibrium.productDist_eq_mul
      (fun j => (Function.update σ i (Convexity.StdSimplex.single a) j).weights) i s
    have hw : othersWeight (fun j => (Function.update σ i (Convexity.StdSimplex.single a)
        j).weights) i s = othersWeight (fun i => (σ i).weights) i s :=
      prod_congr rfl fun l hl => by
        simp only
        rw [Function.update_of_ne (ne_of_mem_erase hl)]
    unfold productDist at hprod
    rw [hprod, hw]
    simp only [Function.update_self, Convexity.StdSimplex.weights_single,
      Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  have hrhs : expectedPayoff u σ i = ∑ s, productDist (fun i => (σ i).weights) s * u i s := rfl
  rw [hlhs, hrhs] at hdev
  simp only [mul_neg, sum_neg_distrib]
  linarith

end NashBridge

end MathlibExt.GameTheory.NashCorrelatedBridge
