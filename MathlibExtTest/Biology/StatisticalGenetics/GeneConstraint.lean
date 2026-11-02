/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.GeneConstraint

@[expose] public section

open Real Set ProbabilityTheory MathlibExt.Biology.StatisticalGenetics.GeneConstraint
open scoped NNReal

namespace MathlibExtTest.Biology.StatisticalGenetics.GeneConstraint

/-! ### LOEUF -/

/-- A gene with `E = 10` expected and no observed LoF variants has `LOEUF = log 20 / 10`. -/
example : loeuf 10 0 = log 20 / 10 := loeuf_zero 10

/-- The flat-prior posterior for `o = 2`, `E = 10` puts mass `95%` below LOEUF. -/
example : (gammaMeasure ((2 : ℕ) + 1) 10).real (Iic (loeuf 10 2)) = 1 - 1 / 20 :=
  gammaMeasure_real_Iic_oeUpper (by norm_num) (by norm_num) (by norm_num) 2

/-- The flat-prior posterior density at `o = 0` is the exponential density of rate `E`. -/
example {E γ : ℝ} (hγ : 0 ≤ γ) :
    E * poissonLik (γ * E) 0 = gammaPDFReal ((0 : ℕ) + 1) E γ :=
  flatPosterior_density E hγ 0

/-- Coverage for a true ratio `γ = 1/2` with `E = 10` (mean `5`). -/
example : 1 - 1 / 20 ≤ (poissonMeasure ((1 / 2 : ℝ≥0) * ⟨10, by norm_num⟩)).real
    {o | ((1 / 2 : ℝ≥0) : ℝ) ≤ loeuf 10 o} :=
  oeUpper_coverage (by norm_num) (by norm_num) (by norm_num) _

/-- More observed variants raise LOEUF; a larger expected count lowers it. -/
example : loeuf 10 1 < loeuf 10 4 ∧ loeuf 20 3 < loeuf 10 3 :=
  ⟨oeUpper_strictMono (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    oeUpper_strictAntiOn (by norm_num) (by norm_num) 3 (by norm_num : (10 : ℝ) ∈ Ioi 0)
      (by norm_num : (20 : ℝ) ∈ Ioi 0) (by norm_num)⟩

/-- Junk value at `E = 0`: division by zero makes the bound `0`; the theorems assume `E > 0`. -/
example (o : ℕ) : loeuf 0 o = 0 := by simp [loeuf, oeUpper]

/-! ### pLI on a three-class model with illustrative rates `1, 1/2, 1/10` -/

/-- Illustrative class rates (not the paper's fitted values). -/
noncomputable def rates : Fin 3 → ℝ := ![1, 1 / 2, 1 / 10]

/-- Equal prior weights. -/
noncomputable def weights : Fin 3 → ℝ := fun _ => 1 / 3

theorem rates_pos : ∀ c, 0 < rates c := by
  intro c; fin_cases c <;> norm_num [rates]

theorem weights_pos : ∀ c, 0 < weights c := fun _ => by norm_num [weights]

theorem rates_min : ∀ c, rates 2 ≤ rates c := by
  intro c; fin_cases c <;> norm_num [rates]

/-- The class posteriors sum to one. -/
example (o : ℕ) : ∑ c, classPosterior weights rates 10 o c = 1 :=
  sum_classPosterior weights_pos rates_pos (by norm_num) o

/-- pLI (the posterior of the most depleted class) strictly decreases with the observed
count. -/
example : classPosterior weights rates 10 5 2 < classPosterior weights rates 10 3 2 :=
  classPosterior_strictAnti weights_pos rates_pos (by norm_num) rates_min
    ⟨0, by norm_num [rates]⟩ (by norm_num)

/-- A two-class value: rates `1` and `1/2`, equal weights, `E = 2`, `o = 0`: the posterior of
the depleted class is `e^{-1} / (e^{-2} + e^{-1})`. -/
example : classPosterior (fun _ : Fin 2 => (1 : ℝ) / 2) ![1, 1 / 2] 2 0 1 =
    exp (-1) / (exp (-2) + exp (-1)) := by
  simp [classPosterior, poissonLik, Fin.sum_univ_two]
  norm_num
  field_simp

end MathlibExtTest.Biology.StatisticalGenetics.GeneConstraint
