/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Reliability.AnnualPoissonLoss
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Examples for annual loss under a Poisson count -/

open MeasureTheory ProbabilityTheory unitInterval
open scoped NNReal

-- Reusing a single nonconstant loss for every occurrence does not require mutual independence.
example :
    let half : I := ⟨1 / 2, by constructor <;> norm_num⟩
    let P := (poissonMeasure 2).prod (bernoulliMeasure (3 : ℝ) (-1) half)
    (∫ ω : ℕ × ℝ, (∑ _i ∈ Finset.range ω.1, ω.2) ∂P) = 2 ∧
      P.real {ω | 0 < ω.1} = 1 - Real.exp (-2) := by
  intro half P
  let ν := bernoulliMeasure (3 : ℝ) (-1) half
  have hN : HasLaw Prod.fst (poissonMeasure 2) P :=
    ⟨measurable_fst.aemeasurable, by simp [P]⟩
  have hL : HasLaw Prod.snd ν P :=
    ⟨measurable_snd.aemeasurable, by simp [P, ν]⟩
  have hInt : Integrable (id : ℝ → ℝ) ν := integrable_bernoulliMeasure _ _ _ _
  have hIndep : IndepFun (Prod.snd : ℕ × ℝ → ℝ) Prod.fst P :=
    (indepFun_prod (μ := poissonMeasure 2) (ν := ν) measurable_id measurable_id).symm
  have h := annual_poisson_loss (P := P) 2 Prod.fst (fun _ => Prod.snd) measurable_fst hN
    (fun _ _ => IdentDistrib.refl measurable_snd.aemeasurable) (hL.integrable hInt) (fun _ => hIndep)
  have hmean : (∫ ω : ℕ × ℝ, ω.2 ∂P) = 1 := by
    rw [hL.integral_eq, integral_bernoulliMeasure]
    norm_num [half, smul_eq_mul]
  have htotal := h.2.1
  rw [hmean, mul_one] at htotal
  exact ⟨by simpa using htotal, by simpa using h.2.2.1⟩

-- Zero intensity implies zero expected annual loss and zero probability of an occurrence.
example :
    let P := poissonMeasure 0
    (∫ n : ℕ, (∑ _i ∈ Finset.range n, (5 : ℝ)) ∂P) = 0 ∧
      P.real {n | 0 < n} = 0 := by
  intro P
  have h := annual_poisson_loss (P := P) 0 (id : ℕ → ℕ) (fun _ _ => 5)
    measurable_id HasLaw.id (fun _ _ => IdentDistrib.refl aemeasurable_const)
    (integrable_const _) (fun _ => indepFun_const_left (5 : ℝ) id)
  exact ⟨by simpa using h.2.1, by simpa using h.2.2.1⟩
