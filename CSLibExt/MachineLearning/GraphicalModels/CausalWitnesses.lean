/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.InterveningVsConditioning
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Causal witnesses: observational equivalence and Simpson reversal

Two finite Boolean networks can have exactly the same observational joint
while an intervention distinguishes them. The kidney-stone network records
Simpson's reversal: treatment B has the higher aggregate success rate, while
treatment A is better for both small and large stones and under intervention.

## References

* J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed., Cambridge
  University Press (2009), §3.2.
* Kidney-stone treatment counts: C. R. Charig, D. R. Webb, S. R. Payne, and
  J. E. A. Wickham, "Comparison of treatment of renal calculi by open
  surgery, percutaneous nephrolithotomy, and extracorporeal shockwave
  lithotripsy", *British Medical Journal* 292 (1986), 879–882,
  doi:10.1136/bmj.292.6524.879. The two-arm success counts by stone size are
  reproduced in S. A. Julious and M. A. Mullee, "Confounding and
  Simpson's paradox", *British Medical Journal* 309 (1994), 1480–1481,
  doi:10.1136/bmj.309.6967.1480. Treatment A below is open surgery and
  treatment B is percutaneous nephrolithotomy: small stones A 81/87,
  B 234/270; large stones A 192/263, B 55/80.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

namespace CausalWitnesses

open Finset Convexity

/-- A three-node copy chain `Z → X → Y` on `Bool`: `Z` is fair, `X = Z`, and
`Y = X` deterministically, with exact parent sets (`pa 0 = ∅`, `pa 1 = {0}`,
`pa 2 = {1}`). -/
noncomputable def copyChainNet : BayesNet Bool 3 where
  pa := fun k => if _ : (k : ℕ) = 0 then ∅
    else if _ : (k : ℕ) = 1 then {⟨0, by omega⟩}
    else {⟨1, by omega⟩}
  cpt k u := if h0 : (k : ℕ) = 0 then
      InterveningVsConditioning.coin (1 / 2) (by norm_num) (by norm_num)
    else if h1 : (k : ℕ) = 1 then
      (if u ⟨⟨0, by omega⟩, by simp [h1]⟩ then
        InterveningVsConditioning.coin 1 (by norm_num) (by norm_num)
      else InterveningVsConditioning.coin 0 (by norm_num) (by norm_num))
    else
      (if u ⟨⟨1, by omega⟩, by simp [h0, h1]⟩ then
        InterveningVsConditioning.coin 1 (by norm_num) (by norm_num)
      else InterveningVsConditioning.coin 0 (by norm_num) (by norm_num))

/-- A three-node common-cause network on `Bool`: `Z` is fair, `X = Z`, and
`Y = Z` deterministically, ignoring `X`, with exact parent sets (`pa 0 = ∅`,
`pa 1 = {0}`, `pa 2 = {0}`). -/
noncomputable def commonCauseNet : BayesNet Bool 3 where
  pa := fun k => if _ : (k : ℕ) = 0 then ∅
    else if _ : (k : ℕ) = 1 then {⟨0, by omega⟩}
    else {⟨0, by omega⟩}
  cpt k u := if h0 : (k : ℕ) = 0 then
      InterveningVsConditioning.coin (1 / 2) (by norm_num) (by norm_num)
    else if h1 : (k : ℕ) = 1 then
      (if u ⟨⟨0, by omega⟩, by simp [h1]⟩ then
        InterveningVsConditioning.coin 1 (by norm_num) (by norm_num)
      else InterveningVsConditioning.coin 0 (by norm_num) (by norm_num))
    else
      (if u ⟨⟨0, by omega⟩, by simp [h0, h1]⟩ then
        InterveningVsConditioning.coin 1 (by norm_num) (by norm_num)
      else InterveningVsConditioning.coin 0 (by norm_num) (by norm_num))

/-- The copy chain and the common-cause network have the same observational
joint law. -/
theorem copyChain_joint_eq_commonCause :
    copyChainNet.joint = commonCauseNet.joint := by
  funext x
  simp only [BayesNet.joint_eq_prod, Fin.prod_univ_three]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp_all [copyChainNet, commonCauseNet,
      InterveningVsConditioning.coin_true, InterveningVsConditioning.coin_false]

/-- Under `do(X = false)`, the copy chain forces `Y = false`. -/
theorem copyChain_intervene_false :
    ∑ x with x 2 = true, (copyChainNet.intervene 1 false).joint x = 0 := by
  rw [Finset.sum_filter, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_intervene]
  simp_rw [show (univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) from by decide]
  simp_rw [prod_pair (show (0 : Fin 3) ≠ 2 by decide)]
  simp [copyChainNet, BayesNet.paVal, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]

/-- Under the same intervention `do(X = false)`, the common-cause network
still has `P(Y = true) = 1 / 2`. -/
theorem commonCause_intervene_false :
    ∑ x with x 2 = true, (commonCauseNet.intervene 1 false).joint x = 1 / 2 := by
  rw [Finset.sum_filter, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_intervene]
  simp_rw [show (univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) from by decide]
  simp_rw [prod_pair (show (0 : Fin 3) ≠ 2 by decide)]
  simp [commonCauseNet, BayesNet.paVal, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]

/-- **Equal observational joints need not determine interventional laws.** -/
theorem equalJoint_interventions_differ :
    copyChainNet.joint = commonCauseNet.joint ∧
      (∑ x with x 2 = true, (copyChainNet.intervene 1 false).joint x) ≠
        ∑ x with x 2 = true, (commonCauseNet.intervene 1 false).joint x := by
  refine ⟨copyChain_joint_eq_commonCause, ?_⟩
  rw [copyChain_intervene_false, commonCause_intervene_false]
  norm_num

/-- The kidney-stone Simpson network on `Bool`: node `0` is a large stone,
node `1` is treatment B, percutaneous nephrolithotomy (with `false`
treatment A, open surgery), and node `2` is success.
The tables encode the 700 patients of Charig et al. (1986), as reproduced by
Julious and Mullee (1994): 357 small and 343 large stones;
treatment B in 270 small and 80 large cases; successes A/B are 81/87 and
234/270 for small stones, and 192/263 and 55/80 for large stones. -/
noncomputable def kidneyNet : BayesNet Bool 3 where
  pa _ := univ
  cpt k u := if h0 : (k : ℕ) = 0 then
      InterveningVsConditioning.coin (49 / 100) (by norm_num) (by norm_num)
    else if h1 : (k : ℕ) = 1 then
      (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then
        InterveningVsConditioning.coin (80 / 343) (by norm_num) (by norm_num)
      else InterveningVsConditioning.coin (90 / 119) (by norm_num) (by norm_num))
    else
      (if u ⟨⟨1, by omega⟩, mem_univ _⟩ then
        (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then
          InterveningVsConditioning.coin (11 / 16) (by norm_num) (by norm_num)
        else InterveningVsConditioning.coin (13 / 15) (by norm_num) (by norm_num))
      else
        (if u ⟨⟨0, by omega⟩, mem_univ _⟩ then
          InterveningVsConditioning.coin (192 / 263) (by norm_num) (by norm_num)
        else InterveningVsConditioning.coin (27 / 29) (by norm_num) (by norm_num)))

theorem kidney_aggregate_B :
    (∑ x with x 1 = true ∧ x 2 = true, kidneyNet.joint x) /
      (∑ x with x 1 = true, kidneyNet.joint x) = 289 / 350 := by
  rw [Finset.sum_filter, Finset.sum_filter,
    InterveningVsConditioning.expand8, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [kidneyNet, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

theorem kidney_aggregate_A :
    (∑ x with x 1 = false ∧ x 2 = true, kidneyNet.joint x) /
      (∑ x with x 1 = false, kidneyNet.joint x) = 273 / 350 := by
  rw [Finset.sum_filter, Finset.sum_filter,
    InterveningVsConditioning.expand8, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [kidneyNet, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

theorem kidney_small_A :
    (∑ x with x 0 = false ∧ x 1 = false ∧ x 2 = true, kidneyNet.joint x) /
      (∑ x with x 0 = false ∧ x 1 = false, kidneyNet.joint x) = 27 / 29 := by
  rw [Finset.sum_filter, Finset.sum_filter,
    InterveningVsConditioning.expand8, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [kidneyNet, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

theorem kidney_small_B :
    (∑ x with x 0 = false ∧ x 1 = true ∧ x 2 = true, kidneyNet.joint x) /
      (∑ x with x 0 = false ∧ x 1 = true, kidneyNet.joint x) = 13 / 15 := by
  rw [Finset.sum_filter, Finset.sum_filter,
    InterveningVsConditioning.expand8, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [kidneyNet, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

theorem kidney_large_A :
    (∑ x with x 0 = true ∧ x 1 = false ∧ x 2 = true, kidneyNet.joint x) /
      (∑ x with x 0 = true ∧ x 1 = false, kidneyNet.joint x) = 192 / 263 := by
  rw [Finset.sum_filter, Finset.sum_filter,
    InterveningVsConditioning.expand8, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [kidneyNet, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

theorem kidney_large_B :
    (∑ x with x 0 = true ∧ x 1 = true ∧ x 2 = true, kidneyNet.joint x) /
      (∑ x with x 0 = true ∧ x 1 = true, kidneyNet.joint x) = 11 / 16 := by
  rw [Finset.sum_filter, Finset.sum_filter,
    InterveningVsConditioning.expand8, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_eq_prod]
  simp_rw [Fin.prod_univ_three]
  simp [kidneyNet, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

/-- **Simpson reversal**: treatment B has the higher aggregate success rate,
while treatment A has the higher success rate in both stone-size strata. -/
theorem kidney_simpson_reversal :
    (∑ x with x 1 = false ∧ x 2 = true, kidneyNet.joint x) /
        (∑ x with x 1 = false, kidneyNet.joint x) <
      (∑ x with x 1 = true ∧ x 2 = true, kidneyNet.joint x) /
        (∑ x with x 1 = true, kidneyNet.joint x) ∧
    (∑ x with x 0 = false ∧ x 1 = true ∧ x 2 = true, kidneyNet.joint x) /
        (∑ x with x 0 = false ∧ x 1 = true, kidneyNet.joint x) <
      (∑ x with x 0 = false ∧ x 1 = false ∧ x 2 = true, kidneyNet.joint x) /
        (∑ x with x 0 = false ∧ x 1 = false, kidneyNet.joint x) ∧
    (∑ x with x 0 = true ∧ x 1 = true ∧ x 2 = true, kidneyNet.joint x) /
        (∑ x with x 0 = true ∧ x 1 = true, kidneyNet.joint x) <
      (∑ x with x 0 = true ∧ x 1 = false ∧ x 2 = true, kidneyNet.joint x) /
        (∑ x with x 0 = true ∧ x 1 = false, kidneyNet.joint x) := by
  rw [kidney_aggregate_A, kidney_aggregate_B, kidney_small_A, kidney_small_B,
    kidney_large_A, kidney_large_B]
  norm_num

/-- The back-door/interventional success probability for treatment A. -/
theorem kidney_intervene_A :
    ∑ x with x 2 = true, (kidneyNet.intervene 1 false).joint x =
      634983 / 762700 := by
  rw [Finset.sum_filter, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_intervene]
  simp_rw [show (univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) from by decide]
  simp_rw [prod_pair (show (0 : Fin 3) ≠ 2 by decide)]
  simp [kidneyNet, BayesNet.paVal, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

/-- The back-door/interventional success probability for treatment B. -/
theorem kidney_intervene_B :
    ∑ x with x 2 = true, (kidneyNet.intervene 1 true).joint x =
      6231 / 8000 := by
  rw [Finset.sum_filter, InterveningVsConditioning.expand8]
  simp_rw [BayesNet.joint_intervene]
  simp_rw [show (univ.erase (1 : Fin 3)) = ({0, 2} : Finset (Fin 3)) from by decide]
  simp_rw [prod_pair (show (0 : Fin 3) ≠ 2 by decide)]
  simp [kidneyNet, BayesNet.paVal, InterveningVsConditioning.coin_true,
    InterveningVsConditioning.coin_false]
  norm_num

/-- Intervention resolves the reversal in favor of treatment A. -/
theorem kidney_intervene_B_lt_A :
    (∑ x with x 2 = true, (kidneyNet.intervene 1 true).joint x) <
      ∑ x with x 2 = true, (kidneyNet.intervene 1 false).joint x := by
  rw [kidney_intervene_A, kidney_intervene_B]
  norm_num

end CausalWitnesses

end Cslib.MachineLearning.GraphicalModels
