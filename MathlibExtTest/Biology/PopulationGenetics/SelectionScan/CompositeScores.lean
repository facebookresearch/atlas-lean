/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.SelectionScan.CompositeScores
public import Mathlib.Tactic.NormNum

@[expose] public section

open Real Finset
open MathlibExt.Biology.PopulationGenetics.SelectionScan

namespace MathlibExtTest.Biology.PopulationGenetics.SelectionScan.CompositeScores

/-! ### A non-vacuous composite-score model

Two binary component statistics. Under selection each takes the value `true` with probability
`3/4`, under neutrality with probability `1/2`; the prior probability of selection is `1/2`. -/

/-- The witness model. -/
noncomputable def model : CompositeModel 2 (fun _ => Bool) where
  prior := 1 / 2
  prior_pos := by norm_num
  prior_lt_one := by norm_num
  sel := fun _ b => if b then 3 / 4 else 1 / 4
  neut := fun _ _ => 1 / 2
  sel_pos := by
    intro i b
    cases b <;> norm_num
  neut_pos := by
    intro i b
    norm_num

/-- Both components favouring selection give the Bayes factor `3/2` each. -/
example (i : Fin 2) : model.bayesFactor i true = 3 / 2 := by
  norm_num [CompositeModel.bayesFactor, model]

/-- The CMS score of the doubly favourable observation is `9/4`. -/
example : model.cms (fun _ => true) = 9 / 4 := by
  norm_num [CompositeModel.cms, CompositeModel.bayesFactor, model, Fin.prod_univ_two]

/-- With a prior of `1/2` the posterior probability of selection is `9/13`. -/
example : model.posterior (fun _ => true) = 9 / 13 := by
  norm_num [CompositeModel.posterior, model, Fin.prod_univ_two]

example : model.posterior (fun _ => true) ∈ Set.Ioo (0 : ℝ) 1 :=
  model.posterior_mem_Ioo _

/-- Posterior odds are prior odds times the score. -/
example : model.posterior (fun _ => true) / (1 - model.posterior (fun _ => true))
    = model.prior / (1 - model.prior) * model.cms (fun _ => true) :=
  model.posterior_odds _

/-- Evidence is additive on the log scale. -/
example : log (model.posterior (fun _ => true) / (1 - model.posterior (fun _ => true)))
    = log (model.prior / (1 - model.prior)) +
      ∑ i, log (model.bayesFactor i ((fun _ => true : ∀ _ : Fin 2, Bool) i)) :=
  model.log_posterior_odds _

/-- A smaller score gives a smaller posterior: the two rankings agree. -/
example : model.posterior (fun _ => false) < model.posterior (fun _ => true) := by
  refine model.posterior_lt_posterior_of_cms_lt _ _ ?_
  norm_num [CompositeModel.cms, CompositeModel.bayesFactor, model, Fin.prod_univ_two]

/-- The model is a probability model on the four possible observations. -/
example : ∑ z : (∀ _ : Fin 2, Bool),
    (model.prior * (∏ i, model.sel i (z i)) + (1 - model.prior) * ∏ i, model.neut i (z i)) = 1 :=
  model.sum_joint_eq_one (by intro i; norm_num [model]) (by intro i; norm_num [model])

/-! ### Sweep escape probabilities and identifiability -/

example : escapeProb 1 0 0 = 0 := (escapeProb_eq_zero_iff one_pos 0 0).mpr rfl

example (y : ℝ) : escapeProb 1 0 y ∈ Set.Ico (0 : ℝ) 1 :=
  escapeProb_mem_Ico zero_le_one 0 y

/-- A lineage one unit away escapes with probability `1 - e⁻¹`. -/
example : escapeProb 1 0 1 = 1 - exp (-1) := by
  norm_num [escapeProb]

/-- Two sweep parameter pairs with the same escape profile coincide. -/
example {α₁ α₂ x₁ x₂ : ℝ} (hα₂ : 0 < α₂)
    (h : ∀ y, escapeProb α₁ x₁ y = escapeProb α₂ x₂ y) : x₁ = x₂ ∧ α₁ = α₂ :=
  escapeProb_inj hα₂ h

/-- A mixture of two distinct site-frequency laws determines its weight. -/
example {p q : ℝ} (h : ∀ b : Bool, p * (if b then 1 else 0) + (1 - p) * (if b then 0 else 1)
    = q * (if b then 1 else 0) + (1 - q) * (if b then 0 else 1)) : p = q := by
  refine mixture_weight_unique (f := fun b : Bool => if b then (1 : ℝ) else 0)
    (g := fun b : Bool => if b then (0 : ℝ) else 1) ?_ h
  intro hfg
  have := congrFun hfg true
  norm_num at this

#print axioms CompositeModel.posterior_odds
#print axioms CompositeModel.sum_joint_eq_one
#print axioms sweep_param_unique

end MathlibExtTest.Biology.PopulationGenetics.SelectionScan.CompositeScores
