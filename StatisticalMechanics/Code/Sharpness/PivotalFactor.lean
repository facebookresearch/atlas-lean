/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.Inequalities.Russo

namespace StatMech

namespace Sharpness

open ConfigSpace Function Finset StatMech

variable {E : Type*} [Fintype E] [DecidableEq E]







noncomputable def openInd (ω : ConfigSpace E) (e : E) : ℝ := if ω e then 1 else 0

omit [Fintype E] [DecidableEq E] in










lemma sign_eq_pivotalFactor_mul_edgeWeight (ω : ConfigSpace E) (e : E) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    (if ω e then (1 : ℝ) else -1)
      = ((openInd ω e - p) / (p * (1 - p))) * edgeWeight p ω e := by
  unfold openInd edgeWeight
  have hp0' : p ≠ 0 := ne_of_gt hp0
  have hp1' : (1 : ℝ) - p ≠ 0 := by linarith
  by_cases h : ω e = true
  · simp only [h, if_true]; field_simp
  · simp only [h, if_false, Bool.false_eq_true]; field_simp; ring











lemma weightOff_mul_sign_eq_pivotalFactor (ω : ConfigSpace E) (e : E) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) :
    weightOff p e ω * (if ω e then (1 : ℝ) else -1)
      = ((openInd ω e - p) / (p * (1 - p))) * configWeight p ω := by
  rw [sign_eq_pivotalFactor_mul_edgeWeight ω e hp0 hp1, configWeight_eq p e ω]
  ring














theorem pivotalProb_eq (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    pivotalProb p A e
      = (1 / (p * (1 - p))) *
          ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
            ((openInd ω e - p) * configWeight p ω) := by
  rw [← russo_per_edge p A hA e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [weightOff_mul_sign_eq_pivotalFactor ω e hp0 hp1]; ring













theorem hasDerivAt_prob_eq_pivotalFactor (A : Set (ConfigSpace E))
    (hA : IsIncreasing A) {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun p => prob p A)
      ((1 / (p * (1 - p))) *
        ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
          ((openInd ω e - p) * configWeight p ω)) p := by
  have h := hasDerivAt_prob_eq_sum_pivotalProb A hA p
  rw [show (1 / (p * (1 - p))) *
        ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
          ((openInd ω e - p) * configWeight p ω)
      = ∑ e, pivotalProb p A e from ?_]
  · exact h
  · rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl (fun e _ => ?_)).symm
    exact pivotalProb_eq A hA e hp0 hp1







theorem deriv_prob_eq_pivotalFactor (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun p => prob p A) p
      = (1 / (p * (1 - p))) *
          ∑ e, ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
            ((openInd ω e - p) * configWeight p ω) :=
  (hasDerivAt_prob_eq_pivotalFactor A hA hp0 hp1).deriv



omit [DecidableEq E] in


lemma configWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : ConfigSpace E) :
    0 ≤ configWeight p ω := by
  unfold configWeight edgeWeight
  apply Finset.prod_nonneg
  intro e _
  by_cases h : ω e <;> simp [h] <;> linarith



lemma pivotalProb_nonneg (A : Set (ConfigSpace E)) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (e : E) : 0 ≤ pivotalProb p A e := by
  unfold pivotalProb
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
    (configWeight_nonneg hp0 hp1 ω)









theorem deriv_prob_nonneg (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ deriv (fun p => prob p A) p := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  exact Finset.sum_nonneg (fun e _ => pivotalProb_nonneg A hp0 hp1 e)

end Sharpness

end StatMech
