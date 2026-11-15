/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CoxBootstrap

@[expose] public section

open Real
open MathlibExt.Probability.Statistics
open MathlibExt.Probability.Statistics.CoxPartialLikelihood
open MathlibExt.Probability.Statistics.CoxBootstrap

namespace MathlibExtTest.Probability.Statistics.CoxBootstrap

/-! ### A concrete Cox estimate

All three observations are at time `1`: an event with covariate `1`, an event with covariate `0`
and a censoring with covariate `0`. Every risk set is the whole sample, the weighted risk-set mean
is `eᵇ / (eᵇ + 2)` and the score is `(1 - eᵇ / (eᵇ + 2)) + (0 - eᵇ / (eᵇ + 2))`, so the Cox
estimate is `log 2`. Everything is computed from the definitions of `coxScore` and `coxMPLE`,
not through the bootstrap theorems. -/

/-- The sample `(1, 1, 1)`, `(1, 1, 0)`, `(1, 0, 0)` (later points are not used at `n = 3`). -/
noncomputable def x₃ : ℕ → ℝ × ℝ × ℝ := fun i =>
  if i = 0 then (1, 1, 1) else if i = 1 then (1, 1, 0) else (1, 0, 0)

theorem riskMean_x₃ (b : ℝ) (i : Fin 3) :
    riskMean (coxArrays fun i : Fin 3 => x₃ i).1 (coxArrays fun i : Fin 3 => x₃ i).2.2 b i =
      exp b / (exp b + 2) := by
  have hrisk : riskSet (coxArrays fun i : Fin 3 => x₃ i).1 i = Finset.univ := by
    ext l
    fin_cases i <;> fin_cases l <;> simp [riskSet, coxArrays, x₃]
  rw [riskMean, hrisk, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [coxArrays, x₃]
  norm_num
  ring

theorem coxScore_x₃ (b : ℝ) :
    coxScore (coxArrays fun i : Fin 3 => x₃ i).1 (coxArrays fun i : Fin 3 => x₃ i).2.1
      (coxArrays fun i : Fin 3 => x₃ i).2.2 b = (2 - exp b) / (exp b + 2) := by
  have hpos : 0 < exp b + 2 := by positivity
  rw [coxScore, Finset.sum_filter, Fin.sum_univ_three]
  simp only [riskMean_x₃]
  simp only [coxArrays, x₃]
  norm_num
  field_simp
  ring

/-- **The Cox estimate of the sample is `log 2`.** -/
theorem coxMPLE_x₃ : coxMPLE x₃ 3 = log 2 := by
  have hroot : coxScore (coxArrays fun i : Fin 3 => x₃ i).1 (coxArrays fun i : Fin 3 => x₃ i).2.1
      (coxArrays fun i : Fin 3 => x₃ i).2.2 (log 2) = 0 := by
    rw [coxScore_x₃, exp_log two_pos]
    norm_num
  have hex : ∃ b, IsMaxOn (logPartialLikelihood₁ (coxArrays fun i : Fin 3 => x₃ i).1
      (coxArrays fun i : Fin 3 => x₃ i).2.1 (coxArrays fun i : Fin 3 => x₃ i).2.2) Set.univ b :=
    ⟨_, CoxAsymptotics.isMaxOn_of_coxScore_eq_zero _ _ _ hroot⟩
  rw [coxMPLE, mple, dite_eq_left hex]
  have h := CoxAsymptotics.coxScore_eq_zero_of_isMaxOn _ _ _ hex.choose_spec
  rw [coxScore_x₃, div_eq_zero_iff] at h
  rcases h with h | h
  · rw [← log_exp hex.choose]
    congr 1
    linarith
  · linarith [exp_pos hex.choose]

/-! ### Boundary: a bootstrap resample with no Cox estimate

Drawing the first point once and the third point twice gives an event with covariate `1` and two
censorings with covariate `0`. Its score `2 / (eᵇ + 2)` is positive, so the partial likelihood is
monotone and has no maximizer: at finite `n` the bootstrap Cox estimate fails to exist with
positive conditional probability, and the bootstrap theorems are only asymptotic. -/

/-- The resample `(1, 1, 1)`, `(1, 0, 0)`, `(1, 0, 0)`. -/
noncomputable def y₃ : ℕ → ℝ × ℝ × ℝ := fun i => if i = 0 then (1, 1, 1) else (1, 0, 0)

theorem coxScore_y₃_pos (b : ℝ) :
    0 < coxScore (coxArrays fun i : Fin 3 => y₃ i).1 (coxArrays fun i : Fin 3 => y₃ i).2.1
      (coxArrays fun i : Fin 3 => y₃ i).2.2 b := by
  have hrisk : ∀ i, riskSet (coxArrays fun i : Fin 3 => y₃ i).1 i = Finset.univ := fun i => by
    ext l
    fin_cases i <;> fin_cases l <;> simp [riskSet, coxArrays, y₃]
  have hR : ∀ i, riskMean (coxArrays fun i : Fin 3 => y₃ i).1
      (coxArrays fun i : Fin 3 => y₃ i).2.2 b i = exp b / (exp b + 2) := fun i => by
    rw [riskMean, hrisk, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [coxArrays, y₃]
    norm_num
    ring
  have hpos : 0 < exp b + 2 := by positivity
  rw [coxScore, Finset.sum_filter, Fin.sum_univ_three]
  simp only [hR]
  simp only [coxArrays, y₃]
  norm_num
  rw [div_lt_one hpos]
  linarith

theorem not_exists_isMaxOn_y₃ :
    ¬ ∃ b, IsMaxOn (logPartialLikelihood₁ (coxArrays fun i : Fin 3 => y₃ i).1
      (coxArrays fun i : Fin 3 => y₃ i).2.1 (coxArrays fun i : Fin 3 => y₃ i).2.2) Set.univ b :=
  fun ⟨b, hb⟩ => (coxScore_y₃_pos b).ne' (CoxAsymptotics.coxScore_eq_zero_of_isMaxOn _ _ _ hb)

/-! ### Non-vacuity: the limit hypotheses hold for a balanced two-level population

One grid time and covariate levels `0, 1`. Under `θ₂`, half the population has each covariate
level, everyone is at risk at the grid time, and each level has an observed event there with
probability `1 / 4`. Then `Ψ(θ₂, b) = 1/4 - eᵇ / (2 (1 + eᵇ))`, so `β₀ = 0` is a root, every
at-risk total is positive and the limiting information is `1 / 8 ≠ 0`: the hypotheses `hpos`,
`hroot` and `hinfo` of the bootstrap theorems are satisfiable. -/

/-- The covariate levels `0, 1`. -/
noncomputable def c₂ : Fin 2 → ℝ := ![0, 1]

/-- The mean indicator vector of the balanced population. -/
noncomputable def θ₂ : Coord 1 2 := WithLp.toLp 2 (Sum.elim (fun _ => 1 / 4) (fun _ => 1 / 2))

theorem scoreMap_θ₂ : scoreMap c₂ θ₂ = fun b => 1 / 4 - exp b / (1 + exp b) / 2 := by
  funext b
  have hpos : 0 < 1 + exp b := by positivity
  simp only [scoreMap, riskSum0, riskSum1, θ₂, c₂, PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr,
    Fin.sum_univ_two, Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num
  field_simp
  ring

theorem hpos_θ₂ (j : Fin 1) : 0 < ∑ a, θ₂ (Sum.inr (j, a)) := by
  simp [θ₂]

theorem hroot_θ₂ : scoreMap c₂ θ₂ 0 = 0 := by
  rw [scoreMap_θ₂]
  norm_num

theorem coxInfo_θ₂ : coxInfo c₂ θ₂ 0 = 1 / 8 := by
  have h : HasDerivAt (fun b => 1 / 4 - exp b / (1 + exp b) / 2)
      (-((exp 0 * (1 + exp 0) - exp 0 * exp 0) / (1 + exp 0) ^ 2 / 2)) 0 :=
    (((hasDerivAt_exp 0).div ((hasDerivAt_exp 0).const_add 1) (by positivity)).div_const
      2).const_sub (1 / 4)
  rw [coxInfo, scoreMap_θ₂, h.deriv]
  norm_num

theorem hinfo_θ₂ : coxInfo c₂ θ₂ 0 ≠ 0 := by
  rw [coxInfo_θ₂]
  norm_num

/-! ### Boundary: a single covariate level carries no information

With one covariate level the risk-set mean of the covariate is that level, so the score map
vanishes identically and the information is `0`: the hypothesis `hinfo` fails and the bootstrap
theorems do not apply (the regression coefficient is not identified). -/

/-- One covariate level, `5`. -/
noncomputable def c₁ : Fin 1 → ℝ := ![5]

/-- Half the population has an event at the grid time; everyone is at risk there. -/
noncomputable def θ₁ : Coord 1 1 := WithLp.toLp 2 (Sum.elim (fun _ => 1 / 2) (fun _ => 1))

theorem scoreMap_θ₁ : scoreMap c₁ θ₁ = fun _ => 0 := by
  funext b
  have hpos : 0 < exp (b * 5) := exp_pos _
  simp only [scoreMap, riskSum0, riskSum1, θ₁, c₁, PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr,
    Finset.univ_unique, Finset.sum_singleton, Matrix.cons_val_zero, Fin.default_eq_zero]
  field_simp
  ring

theorem coxInfo_θ₁ (b : ℝ) : coxInfo c₁ θ₁ b = 0 := by
  rw [coxInfo, scoreMap_θ₁]
  simp

end MathlibExtTest.Probability.Statistics.CoxBootstrap
