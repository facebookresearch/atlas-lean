/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KMRemainder

@[expose] public section

open MeasureTheory Finset
open MathlibExt.Probability.Statistics.CountingProcess
open MathlibExt.Probability.Statistics.CountingProcess.CensoredAtOne

namespace MathlibExtTest.Probability.Statistics.KMRemainder

/-! ### One uncensored subject: the remainder vanishes -/

/-- One subject dying at step `2`, at risk at steps `1` and `2`. -/
def uncN : ℕ → Unit → ℝ := fun n _ => if 2 ≤ n then 1 else 0

/-- At risk exactly while alive: `Y_{k+1} = 1 - N_k`. -/
def uncY : ℕ → Unit → ℝ := fun n _ => if n ≤ 2 then 1 else 0

/-- The uncensored subject satisfies the hypotheses, so `Rₙ = 0` for every hazard and time. -/
example (α : ℕ → ℝ) (n : ℕ) :
    stochasticIntegral (kaplanMeierRemainder uncN uncY α) (fun k _ => α k) n () = 0 :=
  stochasticIntegral_kaplanMeierRemainder_eq_zero_of_uncensored α (by simp [uncN])
    (fun k => by unfold uncN; split_ifs <;> first | omega | norm_num)
    (fun k => by unfold uncN uncY; split_ifs <;> first | omega | norm_num)
    (fun k => by unfold uncN uncY; split_ifs <;> first | omega | norm_num) n

/-- The risk set does empty for the uncensored subject (`Y₃ = 0` with `Δα₃ = 1/2` below), so the
vanishing is not because `1{Y = 0}` never fires: it is `Ŝ₂ = 0` that kills the term. -/
example : uncY 3 () = 0 ∧ kaplanMeierProcess uncN uncY 2 () = 0 := by
  refine ⟨by simp [uncY], ?_⟩
  simp [kaplanMeierProcess, prodIntegral, nelsonAalenProcess, stochasticIntegral, uncN, uncY,
    sum_range_succ, prod_range_succ]

/-! ### The censored-at-time-1 model: values computed from the definitions -/

/-- Censoring breaks the uncensored hypothesis `Y_{k+1} = 1 - N_k`: censored at time `1`, the
subject is not at risk at step `2` yet has not died. -/
example : atRisk 2 (true, true) ≠ 1 - deaths 1 (true, true) := by
  simp [atRisk, deaths]

/-- The Kaplan–Meier process at time `2`: `1` if censored or surviving, `0` after a death. -/
example (c d : Bool) :
    kaplanMeierProcess deaths atRisk 2 (c, d) = if c = false ∧ d = true then 0 else 1 := by
  cases c <;> cases d <;>
    simp [kaplanMeierProcess, prodIntegral, nelsonAalenProcess, stochasticIntegral, deaths,
      atRisk, sum_range_succ, prod_range_succ]

/-- `S₂ = (1 - 0)(1 - 1/2) = 1/2`. -/
example : prodIntegral hazard 2 = 1 / 2 := by
  simp [prodIntegral, hazard, prod_range_succ]; norm_num

/-- Boundary: before the censoring takes effect the remainder is still `0`. -/
example (ω : Ω₀) :
    stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 1 ω =
      0 := by
  simp [stochasticIntegral, kaplanMeierRemainder, atRisk]

/-- The remainder on each outcome: `1` exactly on the censored outcomes. -/
example : stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
      (fun k _ => hazard k) 2 (true, false) = 1 ∧
    stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
      (fun k _ => hazard k) 2 (false, true) = 0 := by
  simp [remainder_two]

/-- No hazard after step `2`, so the remainder does not grow: `R₃ = R₂`. -/
example (ω : Ω₀) :
    stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard) (fun k _ => hazard k) 3 ω =
      if ω.1 = true then 1 else 0 := by
  rw [stochasticIntegral_succ, remainder_two]
  simp [hazard]

/-- The time-`1` σ-algebra sits strictly between the trivial one and everything. -/
example : filtration 1 ≠ ⊥ ∧ filtration 1 ≠ (inferInstance : MeasurableSpace Ω₀) ∧
    filtration 0 = ⊥ ∧
    filtration 2 = (inferInstance : MeasurableSpace Ω₀) :=
  ⟨filtration_one_ne_bot, filtration_one_ne_top, filtration_zero, filtration_of_two_le le_rfl⟩

/-! ### The general theorems on the model -/

/-- The general positivity theorem applies on a censored outcome (`k = 1`: `Y₂ = 0`, `Ŝ₁ = 1`,
`Δα₂ = 1/2`). -/
example (d : Bool) :
    0 < stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
      (fun k _ => hazard k) 2 (true, d) :=
  stochasticIntegral_kaplanMeierRemainder_pos atRisk_mem deaths_le_atRisk hazard_increment_mem
    (k := 1) (by norm_num) (by simp [atRisk])
    (by simp [kaplanMeierProcess, prodIntegral, nelsonAalenProcess, stochasticIntegral, deaths])
    (by rw [hazard_increment]; norm_num)

/-- The general nonnegativity theorem on the model. -/
example (n : ℕ) (ω : Ω₀) :
    0 ≤ stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
      (fun k _ => hazard k) n ω :=
  stochasticIntegral_kaplanMeierRemainder_nonneg atRisk_mem deaths_le_atRisk
    hazard_increment_mem n ω

/-- The general non-vanishing theorem on the model, for the *trivial* σ-algebra
`filtration 0 = ⊥`. -/
example : ¬ μ₀[stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
    (fun k _ => hazard k) 2 | filtration 0] =ᵐ[μ₀] 0 := by
  refine not_condExp_kaplanMeierRemainder_ae_eq_zero atRisk_mem deaths_le_atRisk
    hazard_increment_mem Integrable.of_finite ?_ (filtration.le 0)
  refine lt_of_lt_of_le ?_ (measure_mono (s := {(true, true)}) ?_)
  · simp [μ₀]
  · simp [remainder_two]

/-- Given the trivial σ-algebra the conditional expectation is the mean `E[R₂] = P(c) = 1/2`. -/
example : μ₀[stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
    (fun k _ => hazard k) 2 | filtration 0] = fun _ => 1 / 2 := by
  rw [filtration_zero, condExp_bot', integral_fintype Integrable.of_finite]
  funext ω
  simp only [remainder_two, Fintype.sum_prod_type, Fintype.sum_bool, μ₀_real_singleton,
    probReal_univ]
  norm_num

/-- `E[R₂ | ℱ₁]` evaluated on a censored and an uncensored outcome. -/
example : μ₀[stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
      (fun k _ => hazard k) 2 | filtration 1] (true, true) = 1 ∧
    μ₀[stochasticIntegral (kaplanMeierRemainder deaths atRisk hazard)
      (fun k _ => hazard k) 2 | filtration 1] (false, true) = 0 := by
  simp [condExp_remainder_two]

/-- The Kaplan–Meier estimator is biased in this model: `E[Ŝ₂/S₂] - 1 = 1/2 ≠ 0`. -/
example : ∫ ω, (kaplanMeierProcess deaths atRisk 2 ω / prodIntegral hazard 2 - 1) ∂μ₀ ≠ 0 := by
  rw [integral_kaplanMeierProcess_two_div_sub_one]; norm_num

end MathlibExtTest.Probability.Statistics.KMRemainder
