/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































import Code.Inequalities.Russo

namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]





def openEdge (e : E) : Set (ConfigSpace E) := {ω | ω e = true}

omit [Fintype E] [DecidableEq E] in

lemma openEdge_indicator (e : E) (ω : ConfigSpace E) :
    (openEdge e).indicator (fun _ => (1 : ℝ)) ω = (if ω e then (1 : ℝ) else 0) := by
  classical
  rw [Set.indicator_apply]
  by_cases h : ω e
  · rw [if_pos (show ω ∈ openEdge e from h), if_pos h]
  · rw [if_neg (show ω ∉ openEdge e from h), if_neg h]




lemma sum_weightOff_true_eta (p : ℝ) (e : E) :
    ∑ η : {j : E // j ≠ e} → Bool,
      weightOff p e ((Equiv.funSplitAt e Bool).symm (true, η)) = 1 := by
  have key : ∀ η : {j : E // j ≠ e} → Bool,
      weightOff p e ((Equiv.funSplitAt e Bool).symm (true, η))
      = ∏ j : {x : E // x ≠ e}, (if η j then p else 1 - p) := by
    intro η
    unfold weightOff edgeWeight
    rw [Finset.prod_subtype (univ.erase e) (p := fun x => x ≠ e)
          (fun x => by simp [Finset.mem_erase, and_comm])
          (fun j => if ((Equiv.funSplitAt e Bool).symm (true, η)) j then p else 1 - p)]
    apply Finset.prod_congr rfl
    intro j _
    have hval : ((Equiv.funSplitAt e Bool).symm (true, η)) (j : E) = η j := by
      simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
    rw [hval]
  simp_rw [key]
  rw [← Fintype.prod_sum (fun (j : {x : E // x ≠ e}) (b : Bool) => if b then p else 1 - p)]
  apply Finset.prod_eq_one
  intro j _; rw [Fintype.sum_bool]; simp



lemma sum_filter_true_eq_eta (e : E) (f : ConfigSpace E → ℝ) :
    ∑ ω : ConfigSpace E, (if ω e then f ω else 0)
    = ∑ η : {j : E // j ≠ e} → Bool, f ((Equiv.funSplitAt e Bool).symm (true, η)) := by
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm (fun ω => if ω e then f ω else 0)]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have hT : ∀ η : {j : E // j ≠ e} → Bool,
      ((Equiv.funSplitAt e Bool).symm (true, η)) e = true := fun η => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have hF : ∀ η : {j : E // j ≠ e} → Bool,
      ((Equiv.funSplitAt e Bool).symm (false, η)) e = false := fun η => by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [show (∑ η, if ((Equiv.funSplitAt e Bool).symm (true, η)) e
              then f ((Equiv.funSplitAt e Bool).symm (true, η)) else 0)
        = ∑ η, f ((Equiv.funSplitAt e Bool).symm (true, η)) from by
        apply Finset.sum_congr rfl; intro η _; rw [hT η]; rfl]
  rw [show (∑ η, if ((Equiv.funSplitAt e Bool).symm (false, η)) e
              then f ((Equiv.funSplitAt e Bool).symm (false, η)) else 0)
        = (0 : ℝ) from by
        apply Finset.sum_eq_zero; intro η _; rw [hF η]; rfl]
  ring


lemma sum_weightOff_filter (p : ℝ) (e : E) :
    ∑ ω : ConfigSpace E, (if ω e then weightOff p e ω else 0) = 1 := by
  rw [sum_filter_true_eq_eta e (fun ω => weightOff p e ω)]
  exact sum_weightOff_true_eta p e



lemma prob_openEdge (p : ℝ) (e : E) : prob p (openEdge e) = p := by
  unfold prob
  have step : ∀ ω : ConfigSpace E,
      (openEdge e).indicator (fun _ => (1 : ℝ)) ω * configWeight p ω
      = p * (if ω e then weightOff p e ω else 0) := by
    intro ω
    rw [openEdge_indicator, configWeight_eq p e ω]
    unfold edgeWeight
    by_cases h : ω e <;> simp [h]
  simp_rw [step]
  rw [← Finset.mul_sum, sum_weightOff_filter]; ring





lemma prob_inter_openEdge (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    prob p (A ∩ openEdge e)
    = p * ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0) := by
  unfold prob
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  rw [configWeight_eq p e ω]
  unfold edgeWeight
  classical
  by_cases h : ω e
  · have hmem : ω ∈ A ∩ openEdge e ↔ ω ∈ A := by simp [openEdge, h]
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hA : ω ∈ A
    · simp [hA, (hmem.mpr hA), h]
    · have : ω ∉ A ∩ openEdge e := fun hc => hA hc.1
      simp [hA, this, h]
  · have hnotmem : ω ∉ A ∩ openEdge e := fun hc => h hc.2
    rw [Set.indicator_of_notMem hnotmem]
    simp [h]



lemma prob_decompose (p : ℝ) (A : Set (ConfigSpace E)) (e : E) :
    prob p A
    = p * (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0))
      + (1 - p)
        * (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1)) := by
  unfold prob
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  rw [configWeight_eq p e ω]
  unfold edgeWeight
  by_cases h : ω e <;> simp [h] <;> ring




lemma russo_per_edge_diff (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0))
    - (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1))
    = pivotalProb p A e := by
  rw [← russo_per_edge p A hA e, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω e <;> simp [h]




theorem cov_eq (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A
      = p * (1 - p) * pivotalProb p A e := by
  set Sp := ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (1 : ℝ) else 0)
    with hSp
  set Sm := ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * weightOff p e ω * (if ω e then (0 : ℝ) else 1)
    with hSm
  rw [prob_inter_openEdge p A e, prob_openEdge p e, prob_decompose p A e,
      ← hSp, ← hSm, ← russo_per_edge_diff p A hA e, ← hSp, ← hSm]
  ring



theorem sum_cov_eq (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A)
      = p * (1 - p) * ∑ e, pivotalProb p A e := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun e _ => cov_eq p A hA e)





theorem russoFormula (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    deriv (fun p => prob p A) p
      = (1 / (p * (1 - p)))
          * ∑ e, (prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A) := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p, sum_cov_eq p A hA]
  have hne : p * (1 - p) ≠ 0 := mul_ne_zero hp0 (by intro h; exact hp1 (by linarith))
  field_simp



omit [DecidableEq E] in

lemma configWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ω : ConfigSpace E) :
    0 ≤ configWeight p ω := by
  unfold configWeight edgeWeight
  apply Finset.prod_nonneg
  intro e _
  by_cases h : ω e <;> simp [h] <;> linarith


lemma pivotalProb_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ pivotalProb p A e := by
  unfold pivotalProb
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg
  · classical
    rw [Set.indicator_apply]; split_ifs <;> norm_num
  · exact configWeight_nonneg hp0 hp1 ω





noncomputable def influence (p : ℝ) (A : Set (ConfigSpace E)) (e : E) : ℝ :=
  pivotalProb p A e


lemma influence_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A : Set (ConfigSpace E)) (e : E) : 0 ≤ influence p A e :=
  pivotalProb_nonneg hp0 hp1 A e





theorem cov_ge_influence {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hpl : ε ≤ p) (hpr : p ≤ 1 - ε)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) (e : E) :
    ε * (1 - ε) * influence p A e
      ≤ prob p (A ∩ openEdge e) - prob p (openEdge e) * prob p A := by
  rw [cov_eq p A hA e]
  unfold influence
  have hp0 : 0 ≤ p := le_trans hε0.le hpl
  have hp1 : p ≤ 1 := by linarith
  have hpiv : 0 ≤ pivotalProb p A e := pivotalProb_nonneg hp0 hp1 A e
  have hfac : ε * (1 - ε) ≤ p * (1 - p) := by nlinarith [hε0, hpl, hpr]
  nlinarith [hpiv, hfac]






theorem deriv_ge_total_influence {p ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1/2)
    (hpl : ε ≤ p) (hpr : p ≤ 1 - ε)
    (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    ε * (1 - ε) * ∑ e, influence p A e ≤ deriv (fun p => prob p A) p := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  have hp0 : 0 ≤ p := le_trans hε0.le hpl
  have hp1 : p ≤ 1 := by linarith
  unfold influence
  rw [Finset.mul_sum]
  calc ∑ e, ε * (1 - ε) * pivotalProb p A e
      ≤ ∑ e, p * (1 - p) * pivotalProb p A e := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hfac : ε * (1 - ε) ≤ p * (1 - p) := by nlinarith [hε0, hpl, hpr]
        have hpiv := pivotalProb_nonneg hp0 hp1 A e
        nlinarith [hfac, hpiv]
    _ ≤ ∑ e, pivotalProb p A e := by
        refine Finset.sum_le_sum (fun e _ => ?_)
        have hpiv := pivotalProb_nonneg hp0 hp1 A e
        have hle1 : p * (1 - p) ≤ 1 := by nlinarith [hp0, hp1]
        nlinarith [hle1, hpiv]




theorem deriv_eq_total_influence (p : ℝ) (A : Set (ConfigSpace E)) (hA : IsIncreasing A) :
    deriv (fun p => prob p A) p = ∑ e, influence p A e := by
  rw [deriv_prob_eq_sum_pivotalProb A hA p]
  rfl

end BeffaraDC

end StatMech
