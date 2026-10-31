/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletProcess

@[expose] public section

/-!
# Tests for the stick-breaking construction of the Dirichlet process
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Finset Filter Topology
open scoped ENNReal

namespace MathlibExtTest.Probability.DirichletProcess

/-! ### Deterministic stick breaking -/

/-- Breaking always in half: the `k`-th piece is `(1/2)^(k+1)`. -/
example (k : ℕ) : stickWeight (fun _ ↦ (1 / 2 : ℝ)) k = (1 / 2) ^ (k + 1) := by
  simp only [stickWeight, stickRemainder, prod_const, card_range]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, pow_succ, mul_comm]

private lemma stickRemainder_half :
    stickRemainder (fun _ ↦ (1 / 2 : ℝ)) = fun n ↦ (1 / 2) ^ n :=
  funext fun n ↦ by
    simp only [stickRemainder, prod_const, card_range]
    norm_num

/-- Breaking always in half: the pieces sum to `1`. -/
example : HasSum (stickWeight fun _ ↦ (1 / 2 : ℝ)) 1 := by
  rw [hasSum_stickWeight_iff fun _ ↦ ⟨by norm_num, by norm_num⟩, stickRemainder_half]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Boundary `b ≡ 1`: the whole stick is the first piece. -/
example : stickWeight (fun _ ↦ (1 : ℝ)) 0 = 1 ∧ stickWeight (fun _ ↦ (1 : ℝ)) 1 = 0 := by
  simp [stickWeight, stickRemainder]

/-- Boundary `b ≡ 0`: no piece is ever broken off, the leftover stays `1`, and the pieces do
not sum to `1`. This is why the normalization theorems need the leftover to vanish. -/
example : ¬HasSum (stickWeight fun _ ↦ (0 : ℝ)) 1 := by
  intro h
  have h0 : stickWeight (fun _ ↦ (0 : ℝ)) = 0 := funext fun k ↦ by simp [stickWeight]
  rw [h0] at h
  exact one_ne_zero (h.unique hasSum_zero)

/-- Junk value outside the domain: a "proportion" `2 ∉ [0, 1]` gives a negative second piece,
which `stickBreakingMeasure` reads as weight `0` (`ENNReal.ofReal`). -/
example : stickWeight (fun _ ↦ (2 : ℝ)) 1 = -2 := by
  norm_num [stickWeight, stickRemainder]

/-- The first `n` pieces and the leftover make up the stick, for every `n`. -/
example (n : ℕ) :
    ∑ k ∈ range n, stickWeight (fun _ ↦ (1 / 3 : ℝ)) k + (2 / 3) ^ n = 1 := by
  have h := sum_range_stickWeight_add_stickRemainder (fun _ ↦ (1 / 3 : ℝ)) n
  simp only [stickRemainder, prod_const, card_range] at h
  norm_num at h ⊢
  exact h

/-- With all mass on atom `true`, the stick-breaking measure of `{true}` is the total weight. -/
example : stickBreakingMeasure (fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ true) {true} = 1 := by
  have := isProbabilityMeasure_stickBreakingMeasure (X := Bool)
    (b := fun _ ↦ (1 / 2 : ℝ)) (fun _ ↦ ⟨by norm_num, by norm_num⟩) (by
      rw [hasSum_stickWeight_iff fun _ ↦ ⟨by norm_num, by norm_num⟩, stickRemainder_half]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)) fun _ ↦ true
  rw [← measure_univ (μ := stickBreakingMeasure (fun _ ↦ (1 / 2 : ℝ)) fun _ ↦ true)]
  rw [stickBreakingMeasure_apply _ _ (measurableSet_singleton true),
    stickBreakingMeasure_apply _ _ MeasurableSet.univ]
  simp

/-! ### The Pólya urn predictive -/

/-- After one observation `x ∈ A`, the next lands in `A` with probability
`(α H(A) + 1) / (α + 1)`. -/
example {X : Type*} [MeasurableSpace X] (α : ℝ) (H : Measure X) {A : Set X}
    (hA : MeasurableSet A) {x : X} (hx : x ∈ A) :
    polyaUrnPredictive α H ![x] A = (ENNReal.ofReal α * H A + 1) / ENNReal.ofReal (α + 1) := by
  rw [polyaUrnPredictive_apply α H ![x] hA]
  simp [hx]

/-- With no observations the predictive law is the base measure. -/
example {X : Type*} [MeasurableSpace X] {α : ℝ} (hα : 0 < α) (H : Measure X) {A : Set X}
    (hA : MeasurableSet A) :
    polyaUrnPredictive α H (fun i : Fin 0 ↦ i.elim0) A = H A := by
  rw [polyaUrnPredictive_apply α H _ hA]
  simp only [univ_eq_empty, filter_empty, card_empty, add_zero, CharP.cast_eq_zero]
  rw [mul_comm, ENNReal.mul_div_cancel_right (by simpa using hα) ENNReal.ofReal_ne_top]

/-- Junk value outside the domain: for `α = 0` and no observations, `(α + n)⁻¹ = ∞` multiplies
the zero measure, and the "predictive law" is the zero measure, not a probability measure. -/
example {X : Type*} [MeasurableSpace X] (H : Measure X) :
    polyaUrnPredictive 0 H (fun i : Fin 0 ↦ i.elim0) = 0 := by
  simp [polyaUrnPredictive]

/-! ### Non-vacuity: Sethuraman's canonical model -/

/-- The canonical model with `α = 1` and base measure `δ_true` on `Bool` is a Dirichlet
process: the hypotheses of `StickBreakingProcess.IsDirichlet` are satisfiable. -/
example : (sethuraman 1 one_pos (Measure.dirac true)).IsDirichlet 1 :=
  StickBreakingProcess.isDirichlet_sethuraman 1 one_pos _

/-- For `α = 1` the mean weights are `E[πₖ] = 1 / 2^(k+1)`. -/
example (k : ℕ) :
    ∫ p, (sethuraman 1 one_pos (Measure.dirac true)).weight k p
      ∂sethuramanMeasure 1 one_pos (Measure.dirac true) = 1 / 2 ^ (k + 1) := by
  rw [(StickBreakingProcess.isDirichlet_sethuraman 1 one_pos _).integral_weight]
  norm_num

/-- In the canonical model the random measure is almost surely a probability measure. -/
example : ∀ᵐ p ∂sethuramanMeasure 1 one_pos (Measure.dirac true),
    IsProbabilityMeasure ((sethuraman 1 one_pos (Measure.dirac true)).G p) :=
  (StickBreakingProcess.isDirichlet_sethuraman 1 one_pos _).ae_isProbabilityMeasure_G

/-- A degenerate base measure gives a degenerate process: `Var(G({true})) = 0` for
`H = δ_true`, since `H({true}) = 1`. -/
example : Var[fun p ↦ ((sethuraman 1 one_pos (Measure.dirac true)).G p {true}).toReal;
    sethuramanMeasure 1 one_pos (Measure.dirac true)] = 0 := by
  rw [(StickBreakingProcess.isDirichlet_sethuraman 1 one_pos _).variance_G_apply
    (measurableSet_singleton true)]
  simp [sethuraman, measureReal_def]

/-- The fair coin on `Bool`. -/
noncomputable def coin : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure coin :=
  ⟨by
    simp only [coin, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [ENNReal.add_halves]⟩

/-- For a fair-coin base measure, `Var(G({true})) = (1/2)(1/2)/(α + 1)`; with `α = 1` this
is `1/8`. -/
example : Var[fun p ↦ ((sethuraman 1 one_pos coin).G p {true}).toReal;
    sethuramanMeasure 1 one_pos coin] = 1 / 8 := by
  rw [(StickBreakingProcess.isDirichlet_sethuraman 1 one_pos _).variance_G_apply
    (measurableSet_singleton true)]
  simp [sethuraman, coin, measureReal_def]
  norm_num

/-- Two draws from `DP(1, H)` pick the same atom with probability `1/2`. -/
example : (sethuraman 1 one_pos (Measure.dirac true)).sumSqWeight = ENNReal.ofReal (1 / 2) := by
  rw [(StickBreakingProcess.isDirichlet_sethuraman 1 one_pos _).sumSqWeight_eq]
  norm_num

/-- The mean of the Dirichlet-process law: `E[ν({true})] = H({true})`. -/
example : ∫⁻ ν, ν {true} ∂dirichletProcess 1 one_pos (Measure.dirac true) = 1 := by
  rw [lintegral_dirichletProcess_apply 1 one_pos _ (measurableSet_singleton true)]
  simp

#print axioms StickBreakingProcess.IsDirichlet.integral_weight
#print axioms StickBreakingProcess.IsDirichlet.ae_isProbabilityMeasure_G
#print axioms StickBreakingProcess.IsDirichlet.lintegral_G_mul_G_eq_predictive
#print axioms StickBreakingProcess.IsDirichlet.variance_G_apply
#print axioms StickBreakingProcess.isDirichlet_sethuraman
#print axioms lintegral_dirichletProcess_apply
#print axioms StickBreakingProcess.ae_hasSum_weight
#print axioms StickBreakingProcess.lintegral_G_mul_G
#print axioms StickBreakingProcess.IsDirichlet.sumSqWeight_eq

end MathlibExtTest.Probability.DirichletProcess
