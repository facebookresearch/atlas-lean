/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.ConformalizedQuantileRegression
public import MathlibExt.Probability.Distributions.BetaBinomialSampleRank
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory MathlibExt.Probability.Statistics.SplitConformal
  MathlibExt.Probability.Statistics.SplitConformalExactCoverage
  MathlibExt.Probability.Statistics.ConformalizedQuantileRegression
  MathlibExt.Probability.Distributions.BetaBinomialSampleRank

namespace MathlibExtTest.Probability.Statistics.ConformalizedQuantileRegression

/-! ### The band -/

/-- A finite threshold gives the interval `[q_lo x - Q, q_hi x + Q]`. -/
example : cqrBand (fun _ : ℝ => (0 : ℝ)) (fun _ => 1) ((1 / 2 : ℝ) : WithTop ℝ) 7 =
    Set.Icc (-1 / 2) (3 / 2) := by
  rw [cqrBand_coe]; norm_num

/-- The infinite threshold gives all of `ℝ`. -/
example (y : ℝ) : y ∈ cqrBand (fun _ : ℝ => (0 : ℝ)) (fun _ => 1) ⊤ 7 :=
  (mem_cqrBand_iff _ _ _ _ _).2 le_top

/-- A point strictly inside the fitted quantile band has a negative score. -/
example : cqrScore (fun _ : ℝ => (0 : ℝ)) (fun _ => 1) (7, 1 / 2) = -1 / 2 := by
  norm_num [cqrScore]

/-! ### Theorem 1 of Romano, Patterson and Candès is not vacuous -/

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev unifIcc : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unifIcc := ⟨by simp [unifIcc]⟩

/-- Data `Z i = (ω i, 2 ω i)` with `ω` i.i.d. uniform: an exchangeable law on `(ℝ × ℝ)^(n+1)`. -/
noncomputable abbrev dataLaw (n : ℕ) : Measure (Fin (n + 1) → ℝ × ℝ) :=
  (Measure.pi fun _ : Fin (n + 1) => unifIcc).map fun ω i => (ω i, 2 * ω i)

theorem measurable_data (n : ℕ) :
    Measurable fun (ω : Fin (n + 1) → ℝ) (i : Fin (n + 1)) => (ω i, 2 * ω i) :=
  Measurable.of_eval fun i => (measurable_pi_apply i).prodMk
    (measurable_const.mul (measurable_pi_apply i))

theorem dataLaw_perm (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    (dataLaw n).map (fun Z => Z ∘ σ) = dataLaw n := by
  have hσℝ : Measurable fun ω : Fin (n + 1) → ℝ => ω ∘ σ :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  have hσZ : Measurable fun Z : Fin (n + 1) → ℝ × ℝ => Z ∘ σ :=
    Measurable.of_eval fun i => measurable_pi_apply (σ i)
  rw [dataLaw, Measure.map_map hσZ (measurable_data n)]
  conv_rhs => rw [← map_comp_perm_pi unifIcc σ]
  rw [Measure.map_map (measurable_data n) hσℝ]
  rfl

/-- Lower bound: `n = 9`, `α = 1/10`. -/
example :
    ENNReal.ofReal (1 - 1 / 10) ≤
      dataLaw 9 {Z | (Z (Fin.last 9)).2 ∈ cqrBand id (fun x => 3 * x)
        (cqrThreshold id (fun x => 3 * x) ⌈(1 - (1 / 10 : ℝ)) * ((9 : ℕ) + 1)⌉₊ Z)
        (Z (Fin.last 9)).1} :=
  ofReal_one_sub_le_measure_mem_cqrBand _ (dataLaw_perm 9) measurable_id
    (show Measurable (fun x : ℝ => 3 * x) from measurable_const.mul measurable_id) (by norm_num) (by norm_num)

/-- Upper bound: with `q_lo = id`, `q_hi = 3 ·` the score of `(ω, 2 ω)` is `-ω`, so the scores
are almost surely distinct and all hypotheses hold together. -/
example :
    dataLaw 9 {Z | (Z (Fin.last 9)).2 ∈ cqrBand id (fun x => 3 * x)
        (cqrThreshold id (fun x => 3 * x) ⌈(1 - (1 / 10 : ℝ)) * ((9 : ℕ) + 1)⌉₊ Z)
        (Z (Fin.last 9)).1} ≤ ENNReal.ofReal (1 - 1 / 10 + 1 / ((9 : ℕ) + 1)) := by
  have hscore : ∀ t : ℝ, cqrScore id (fun x => 3 * x) (t, 2 * t) = -t := by
    intro t
    simp only [cqrScore, id]
    rw [max_eq_left (by linarith)]
    ring
  refine measure_mem_cqrBand_le _ (dataLaw_perm 9) measurable_id
    (show Measurable (fun x : ℝ => 3 * x) from measurable_const.mul measurable_id) ?_ (by norm_num) (by norm_num)
  have hS : MeasurableSet {Z : Fin (9 + 1) → ℝ × ℝ |
      Function.Injective fun i => cqrScore id (fun x => 3 * x) (Z i)} := by
    have hv : Measurable fun (Z : Fin (9 + 1) → ℝ × ℝ) (i : Fin (9 + 1)) =>
        cqrScore id (fun x => 3 * x) (Z i) := by
      refine Measurable.of_eval fun i => ?_
      have h1 := measurable_fst.comp (measurable_pi_apply (X := fun _ : Fin (9 + 1) => ℝ × ℝ) i)
      have h2 := measurable_snd.comp (measurable_pi_apply (X := fun _ : Fin (9 + 1) => ℝ × ℝ) i)
      exact (h1.sub h2).max (h2.sub (measurable_const.mul h1))
    exact hv measurableSet_setOf_injective
  rw [dataLaw, ae_map_iff (measurable_data 9).aemeasurable hS]
  filter_upwards [ae_injective_pi (ι := Fin (9 + 1)) unifIcc] with ω hω
  intro i j h
  simp only [hscore, neg_inj] at h
  exact hω h

end MathlibExtTest.Probability.Statistics.ConformalizedQuantileRegression
