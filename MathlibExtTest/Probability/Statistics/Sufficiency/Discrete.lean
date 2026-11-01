/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Discrete

@[expose] public section

open MathlibExt.Probability.Statistics.Sufficiency
open scoped ENNReal NNReal

namespace MathlibExtTest.Probability.Statistics.Sufficiency.Discrete

/-- Mass of one coin toss with success probability `θ`. -/
noncomputable def coin (θ : ℝ≥0) (b : Bool) : ℝ≥0 := if b then θ else 1 - θ

/-- Two independent tosses of a coin with success probability `θ ∈ [0, 1]`. -/
noncomputable def twoCoins (θ : {θ : ℝ≥0 // θ ≤ 1}) : PMF (Bool × Bool) :=
  PMF.ofFintype (fun x => ((coin θ x.1 * coin θ x.2 : ℝ≥0) : ℝ≥0∞)) (by
    have h : coin θ true + coin θ false = 1 := by
      simp [coin, add_tsub_cancel_of_le θ.2]
    rw [← ENNReal.ofNNReal_finsetSum, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, ← mul_add, h, mul_one, ENNReal.coe_one])

/-- The number of successes. -/
def heads (x : Bool × Bool) : ℕ := x.1.toNat + x.2.toNat

/-- Non-vacuity: the number of successes is sufficient for two Bernoulli tosses, through the
factorization `P_θ(x) = θ^k (1 - θ)^(2 - k) · 1` with `k` the number of successes. -/
theorem heads_sufficient : IsSufficientPMF twoCoins heads := by
  refine isSufficientPMF_of_factorization (fun θ k => (θ : ℝ≥0) ^ k * (1 - θ) ^ (2 - k))
    (fun _ => 1) fun θ x => ?_
  rcases x with ⟨_ | _, _ | _⟩ <;>
    simp [twoCoins, coin, heads, pow_two, mul_comm]

/-- The constant statistic is not sufficient: under `θ = 1/2` and `θ = 1/4` the elementary
conditional law (here the law itself) differs at `(true, true)`. -/
theorem const_not_sufficient : ¬ IsSufficientPMF twoCoins (fun _ => ()) := by
  intro h
  have h4 : (1 / 4 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num)]
    norm_num
  have h2 : (1 / 2 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num)]
    norm_num
  have hm : ∀ θ, (twoCoins θ).map (fun _ => ()) () = 1 := fun θ => by
    rw [PMF.map_apply]
    simpa using (twoCoins θ).tsum_coe
  have key := h ⟨1 / 2, h2⟩ ⟨1 / 4, h4⟩ (true, true) (by rw [hm]; simp) (by rw [hm]; simp)
  rw [hm, hm, div_one, div_one] at key
  simp only [twoCoins, PMF.ofFintype_apply, coin, ite_true, ENNReal.coe_inj] at key
  norm_num at key

/-- Factorization recovered from sufficiency: the `h` it produces is a conditional probability,
so it lies in `[0, 1]`. -/
example : ∃ h : Bool × Bool → ℝ≥0, (∀ x, h x ≤ 1) ∧
    ∀ θ x, twoCoins θ x = (twoCoins θ).map heads (heads x) * (h x : ℝ≥0∞) :=
  heads_sufficient.factorization

end MathlibExtTest.Probability.Statistics.Sufficiency.Discrete
