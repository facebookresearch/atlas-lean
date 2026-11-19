/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Epidemiology.EarlyEpidemicFinalSize
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset Real
open scoped ENNReal
open MathlibExt.Probability MathlibExt.Probability.GaltonWatson
open MathlibExt.Biology.Epidemiology.EarlyEpidemicBranching
open MathlibExt.Biology.Epidemiology.EarlyEpidemicFinalSize

namespace MathlibExtTest.Biology.Epidemiology.EarlyEpidemicFinalSize

/-! ### Final size on concrete data

All values are computed by evaluating the definitions. Every infective makes two contacts. -/

/-- Depletion: susceptibles `{1, 2, 3}`, contact `j` goes to individual `j + 1`. Generation sizes
`1, 2, 1, 0`; the whole of `S₀` is infected, using `2 + 4 + 2 = 8` contacts. -/
example : finalSize (fun _ _ => 2) (fun j => j + 1) ({1, 2, 3} : Finset ℕ) = 3 := by decide
example : totalContacts (fun _ _ => 2) (fun j => j + 1) ({1, 2, 3} : Finset ℕ) = 8 := by decide

/-- Repeated targets: every contact goes to individual `1`; only the first contact infects, so
one individual is infected and `2 + 2 = 4` contacts are made. -/
example : finalSize (fun _ _ => 2) (fun _ => 1) ((range 10).erase 0) = 1 := by decide
example : totalContacts (fun _ _ => 2) (fun _ => 1) ((range 10).erase 0) = 4 := by decide

/-- The same outbreaks in the population `Fin 10`, with the hits, outside contacts and repeated
contacts of the first `c` contacts: of the `8` contacts of the depletion example, `3` hit and
the `5` others go outside `S₀`. -/
example : hits ({1, 2, 3} : Finset (Fin 10)) (fun j => Fin.ofNat 10 (j + 1)) 8 = 3 := by
  decide
example : outsideContacts ({1, 2, 3} : Finset (Fin 10)) (fun j => Fin.ofNat 10 (j + 1)) 8 = 5 := by
  decide
example : repeatContacts (fun j => Fin.ofNat 10 (j + 1)) 8 = 0 := by decide
example : hits ({1, 2, 3} : Finset (Fin 10)) (fun _ => 1) 4 = 1 := by decide
example : repeatContacts (fun _ => (1 : Fin 10)) 4 = 3 := by decide

/-! ### The final-size equation -/

/-- `0` always solves the final-size equation (the minor-outbreak root). -/
example (R : ℝ) : finalSizeGap R 0 = 0 := by simp [finalSizeGap]

/-- For `R ≤ 1` there is no positive root and `finalSizeRoot` is `0` by definition. -/
example : finalSizeRoot 1 = 0 := by simp [finalSizeRoot]

private lemma exp_eight_fifths_lt_five : exp (8 / 5) < 5 := by
  have h1 : exp (8 / 5) ^ 5 = exp 1 ^ 8 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
  have h2 : exp 1 ^ 8 < 5 ^ 5 :=
    calc exp 1 ^ 8 < 2.7182818286 ^ 8 := by gcongr; exact Real.exp_one_lt_d9
      _ < 5 ^ 5 := by norm_num
  exact lt_of_pow_lt_pow_left₀ 5 (by norm_num) (h1 ▸ h2)

private lemma ten_thirds_lt_exp_seven_fifths : 10 / 3 < exp (7 / 5) := by
  have h1 : exp (7 / 5) = exp 1 * exp (2 / 5) := by rw [← Real.exp_add]; norm_num
  have h2 : (2 / 5 : ℝ) + 1 ≤ exp (2 / 5) := add_one_le_exp _
  have h3 := Real.exp_one_gt_d9
  rw [h1]
  nlinarith [exp_pos (2 / 5 : ℝ)]

/-- **The root for `R₀ = 2`.** `τ = finalSizeRoot 2 ∈ (7/10, 4/5)` (numerically `τ ≈ 0.7968`):
the final-size function changes sign on `[7/10, 4/5]`, so it has a root there, and `τ` is the
only positive root. -/
theorem finalSizeRoot_two_mem : finalSizeRoot 2 ∈ Set.Ioo (7 / 10 : ℝ) (4 / 5) := by
  have hlo : 0 < finalSizeGap 2 (7 / 10) := by
    unfold finalSizeGap
    have : exp (-(2 * (7 / 10 : ℝ))) = (exp (7 / 5))⁻¹ := by rw [← Real.exp_neg]; norm_num
    rw [this]
    have h := ten_thirds_lt_exp_seven_fifths
    have : (exp (7 / 5))⁻¹ < 3 / 10 := by
      rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]; linarith
    linarith
  have hhi : finalSizeGap 2 (4 / 5) < 0 := by
    unfold finalSizeGap
    have : exp (-(2 * (4 / 5 : ℝ))) = (exp (8 / 5))⁻¹ := by rw [← Real.exp_neg]; norm_num
    rw [this]
    have : 1 / 5 < (exp (8 / 5))⁻¹ := by
      rw [lt_inv_comm₀ (by norm_num) (exp_pos _)]; linarith [exp_eight_fifths_lt_five]
    linarith
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Ioo' (by norm_num : (7 / 10 : ℝ) ≤ 4 / 5)
    (continuous_finalSizeGap 2).continuousOn ⟨hhi, hlo⟩
  have hroot : x = finalSizeRoot 2 := eq_finalSizeRoot (by norm_num) (by linarith [hx.1])
    (by unfold finalSizeGap at hgx; linarith)
  exact hroot ▸ hx

/-! ### A non-vacuous instance

Two contacts per infective (`ν = δ₂`, `R₀ = 2`, variance `0`, extinction probability `0`), in
the canonical model on `Fin (k + 1)` with everyone initially susceptible. -/

theorem integrable_sq_dirac_two : Integrable (fun k : ℕ => (k : ℝ) ^ 2) (Measure.dirac 2) :=
  (integrable_const ((2 : ℕ) ^ 2 : ℝ)).congr (by
    rw [ae_dirac_eq]; exact Filter.eventually_pure.2 (by norm_num))

theorem mean_dirac_two : mean (Measure.dirac 2) = 2 := by
  rw [mean, lintegral_dirac]; norm_num

theorem extinctionProb_dirac_two : extinctionProb (Measure.dirac 2) = 0 := by
  have hq := isLeast_extinctionProb (Measure.dirac 2)
  refine le_antisymm (hq.2 ⟨⟨le_rfl, zero_le_one⟩, ?_⟩) hq.1.1.1
  rw [pgf_def, integral_dirac]; norm_num

/-- The hypotheses of the final-size theorem hold, and its conclusion is a genuine limit: the
fraction ultimately infected concentrates at `τ ∈ (7/10, 4/5)` with probability tending to
`1 - q = 1`. -/
example {δ : ℝ} (hδ : 0 < δ) (hδτ : δ < finalSizeRoot 2) :
    Tendsto (fun k => (canonicalMeasure (Measure.dirac 2) (k + 1)).real
      {ω | |(finalSize (fun n i => ω.1 (n, i)) (fun j => ω.2 j) univ : ℝ) / (k + 1 : ℕ) -
        finalSizeRoot 2| < δ}) atTop (𝓝 1) := by
  have h := tendsto_measureReal_abs_finalSize_div_sub_lt
    (P := fun k => canonicalMeasure (Measure.dirac 2) (k + 1)) (N := fun k => k + 1)
    (S₀ := fun _ => univ) (fun k => isFinalSizeEpidemic_canonical (Measure.dirac 2) (k + 1))
    integrable_sq_dirac_two (by rw [mean_dirac_two]; norm_num)
    (tendsto_add_atTop_nat 1) (by simp) hδ (by rw [mean_dirac_two]; simpa using hδτ)
  rw [mean_dirac_two, extinctionProb_dirac_two, sub_zero] at h
  simpa using h

end MathlibExtTest.Biology.Epidemiology.EarlyEpidemicFinalSize
