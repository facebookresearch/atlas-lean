/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DeMoivreLaplace
public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology unitInterval

namespace MathlibExtTest.Probability.DeMoivreLaplace

/-- The `{0, 1}`-valued coin flip on `Bool`: `1` on `true`, `0` on `false`. -/
def coin : Bool → ℝ := fun b => if b then 1 else 0

/-- The coin is measurable (every function out of the discrete `Bool` is). -/
theorem measurable_coin : Measurable coin := by
  unfold coin
  fun_prop

/-- The coin takes values in `{0, 1}` everywhere. -/
theorem coin_mem_zero_one (b : Bool) : coin b = 0 ∨ coin b = 1 := by
  cases b <;> simp [coin]

/-- The fair Bernoulli parameter, as an element of the unit interval. -/
noncomputable def half : I := ⟨(1 / 2 : ℝ), by norm_num, by norm_num⟩

/-- The mean of a fair coin flip is `1 / 2`. -/
theorem integral_coin_fair :
    ∫ b, coin b ∂Ber(true, false, half) = 1 / 2 := by
  rw [integral_bernoulliMeasure]
  simp [coin, half]

/-- The coin-flip helpers apply to a fair coin: it is integrable and
`∫ coin² = ∫ coin`. -/
theorem integrable_coin_fair :
    Integrable coin Ber(true, false, half) :=
  integrable_of_ae_eq_zero_or_one measurable_coin.aemeasurable
    (Filter.Eventually.of_forall coin_mem_zero_one)

theorem integral_sq_coin_fair :
    ∫ b, (coin b) ^ 2 ∂Ber(true, false, half)
      = ∫ b, coin b ∂Ber(true, false, half) :=
  integral_sq_eq_integral_of_ae_eq_zero_or_one
    (Filter.Eventually.of_forall coin_mem_zero_one)

/-- The standardized sum at `n = 0` is `0`. -/
theorem standardized_zero {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (p : ℝ) (ω : Ω) :
    deMoivreLaplaceStandardized X p 0 ω = 0 := by
  simp [deMoivreLaplaceStandardized]

/-- The fair-coin product space: `ℕ → Bool` with the product of fair
Bernoulli measures. -/
noncomputable def fairCoinSpace : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => Ber(true, false, half))

/-- The product of probability measures is a probability measure. -/
instance : IsProbabilityMeasure fairCoinSpace := by
  rw [fairCoinSpace]
  infer_instance

/-- The coordinate coin flips on the product space. -/
def fairCoinSeq : ℕ → (ℕ → Bool) → ℝ := fun i => coin ∘ fun ω => ω i

/-- The coordinate flips are `{0, 1}`-valued everywhere. -/
theorem fairCoinSeq_mem_zero_one (i : ℕ) :
    ∀ᵐ ω ∂fairCoinSpace, fairCoinSeq i ω = 0 ∨ fairCoinSeq i ω = 1 :=
  Filter.Eventually.of_forall fun ω => coin_mem_zero_one (ω i)

/-- Each coordinate flip has mean `1 / 2`. -/
theorem integral_fairCoinSeq (i : ℕ) :
    ∫ ω, fairCoinSeq i ω ∂fairCoinSpace = 1 / 2 := by
  show ∫ ω, coin (ω i) ∂fairCoinSpace = 1 / 2
  have hmap : fairCoinSpace.map (fun ω : ℕ → Bool => ω i)
      = Ber(true, false, half) := by
    rw [fairCoinSpace, Measure.infinitePi_map_eval]
  have hmeas : AEMeasurable (fun ω : ℕ → Bool => ω i) fairCoinSpace :=
    (measurable_pi_apply i).aemeasurable
  have hstrong : AEStronglyMeasurable coin
      (fairCoinSpace.map (fun ω : ℕ → Bool => ω i)) :=
    measurable_coin.aestronglyMeasurable
  rw [← integral_map hmeas hstrong, hmap]
  exact integral_coin_fair

/-- The coordinate flips are independent. -/
theorem iIndepFun_fairCoinSeq : iIndepFun fairCoinSeq fairCoinSpace :=
  iIndepFun_infinitePi (fun _ => measurable_coin)

/-- The coordinate flips are identically distributed. -/
theorem identDistrib_fairCoinSeq (i : ℕ) :
    IdentDistrib (fairCoinSeq i) (fairCoinSeq 0) fairCoinSpace fairCoinSpace := by
  have hmap_eq (j : ℕ) : fairCoinSpace.map (fairCoinSeq j)
      = (Ber(true, false, half)).map coin := by
    have h1 : fairCoinSpace.map (fun ω : ℕ → Bool => ω j)
        = Ber(true, false, half) := by
      rw [fairCoinSpace, Measure.infinitePi_map_eval]
    calc fairCoinSpace.map (fairCoinSeq j)
        = fairCoinSpace.map (coin ∘ fun ω : ℕ → Bool => ω j) := rfl
      _ = (fairCoinSpace.map (fun ω : ℕ → Bool => ω j)).map coin := by
          rw [Measure.map_map measurable_coin (measurable_pi_apply j)]
      _ = (Ber(true, false, half)).map coin := by rw [h1]
  refine ⟨(measurable_coin.comp (measurable_pi_apply i)).aemeasurable,
    (measurable_coin.comp (measurable_pi_apply 0)).aemeasurable, ?_⟩
  rw [hmap_eq i, hmap_eq 0]

/-- End-to-end check: the De Moivre–Laplace interval form applies to fair
coin flips, so the standardized sums' mass on `[-1, 1]` tends to the
standard normal mass of `[-1, 1]`. -/
theorem deMoivreLaplace_fair_coin :
    Tendsto (fun n => fairCoinSpace.real
        {ω | (-1 : ℝ) ≤ deMoivreLaplaceStandardized fairCoinSeq (1 / 2) n ω
          ∧ deMoivreLaplaceStandardized fairCoinSeq (1 / 2) n ω ≤ 1}) atTop
      (𝓝 ((gaussianReal 0 1).real (Set.Icc (-1 : ℝ) 1))) := by
  refine deMoivreLaplace_interval_probability fairCoinSeq (by norm_num) (by norm_num)
    fairCoinSeq_mem_zero_one integral_fairCoinSeq iIndepFun_fairCoinSeq
    identDistrib_fairCoinSeq (by norm_num)

end MathlibExtTest.Probability.DeMoivreLaplace
