/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































































import Code.OSSS.AdaptiveTau

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace AdaptMConditional

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.LindebergTree OSSS.AdaptiveTau

variable {E : Type*} [Fintype E] [DecidableEq E]










def mixUV {n : ℕ} (U V : Fin n → ℝ) (m : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < m then U i else V i



def adaptWt {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < t then V i else if (i : ℕ) < m then U i else V i



lemma adaptWt_eq_Wt_mix {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) :
    adaptWt U V m t = Wt (mixUV U V m) V t := by
  funext i
  unfold adaptWt Wt mixUV
  by_cases ht : (i : ℕ) < t
  · simp [ht]
  · simp [ht]


lemma adaptWt_zero {n : ℕ} (U V : Fin n → ℝ) (m : ℕ) :
    adaptWt U V m 0 = mixUV U V m := by
  funext i; unfold adaptWt mixUV; simp


lemma adaptWt_card {n : ℕ} (U V : Fin n → ℝ) (m : ℕ) :
    adaptWt U V m n = V := by
  funext i; unfold adaptWt; simp [i.2]


lemma adaptWt_ge_stop {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) (htm : m ≤ t) :
    adaptWt U V m t = V := by
  funext i
  unfold adaptWt
  by_cases ht : (i : ℕ) < t
  · simp [ht]
  · have : ¬ (i : ℕ) < m := by omega
    simp [ht, this]


lemma adaptWt_agree_off {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) (ht : 1 ≤ t) :
    ∀ i : Fin n, (i : ℕ) ≠ t - 1 → adaptWt U V m t i = adaptWt U V m (t-1) i := by
  intro i hi
  unfold adaptWt
  by_cases h : (i : ℕ) < t
  · have h' : (i : ℕ) < t - 1 := by omega
    simp [h, h']
  · have h' : ¬ (i : ℕ) < t - 1 := by omega
    simp [h, h']


lemma adaptWt_at_pos {n : ℕ} (U V : Fin n → ℝ) (m t : ℕ) (ht : 1 ≤ t) (htm : t ≤ m)
    (htn : t - 1 < n) :
    adaptWt U V m t ⟨t-1, htn⟩ = V ⟨t-1, htn⟩ ∧ adaptWt U V m (t-1) ⟨t-1, htn⟩ = U ⟨t-1, htn⟩ := by
  unfold adaptWt
  refine ⟨?_, ?_⟩
  · have h : (⟨t-1, htn⟩ : Fin n).val < t := by show t - 1 < t; omega
    simp [h]
  · have h1 : ¬ (⟨t-1, htn⟩ : Fin n).val < t - 1 := by show ¬ t - 1 < t - 1; exact lt_irrefl _
    have h2 : (⟨t-1, htn⟩ : Fin n).val < m := by show t - 1 < m; omega
    simp only [h1, if_false, h2, if_true]











def detAtC {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ) (X : ConfigSpace E) (t : ℕ) :
    Prop :=
  ∀ w : ConfigSpace E, (∀ e ∈ prefixSet σ t, w e = X e) → f w = f X


lemma detAtC_card {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (X : ConfigSpace E) :
    detAtC (σ : Fin n → E) f X n := by
  intro w hw
  have hall : ∀ e, w e = X e := by
    intro e; exact hw e (by rw [prefixSet_card σ]; exact Finset.mem_univ e)
  rw [funext hall]



noncomputable instance detAtC_decPred {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) : DecidablePred (detAtC σ f X) :=
  fun t => Classical.propDecidable (detAtC σ f X t)



noncomputable def stopValC {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (X : ConfigSpace E) : ℕ :=
  Nat.find (⟨n, detAtC_card σ f X⟩ : ∃ t, detAtC (σ : Fin n → E) f X t)




noncomputable def stopVal (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) : ℕ :=
  stopValC σ f (codeMap μ (σ : Fin n → E) U)


lemma stopVal_eq_stopValC (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) :
    stopVal μ σ f U = stopValC σ f (codeMap μ (σ : Fin n → E) U) := rfl


lemma stopVal_le (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (U : Fin n → ℝ) : stopVal μ σ f U ≤ n :=
  Nat.find_le (detAtC_card σ f (codeMap μ (σ : Fin n → E) U))



lemma stopVal_determines (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) :
    detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) U) (stopVal μ σ f U) :=
  Nat.find_spec (⟨n, detAtC_card σ f (codeMap μ (σ : Fin n → E) U)⟩ :
    ∃ t, detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) U) t)









lemma codeMap_agree_on_prefix (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (w w' : Fin n → ℝ) (k : ℕ)
    (hagree : ∀ i : Fin n, (i : ℕ) < k → w i = w' i) :
    ∀ e ∈ prefixSet (σ : Fin n → E) k,
      codeMap μ (σ : Fin n → E) w e = codeMap μ (σ : Fin n → E) w' e := by
  intro e he
  rw [mem_prefixSet_iff] at he
  obtain ⟨i, hik, rfl⟩ := he
  
  have hstab : ∀ v : Fin n → ℝ,
      codeMap μ (σ : Fin n → E) v ((σ : Fin n → E) i)
        = codePrefix μ (σ : Fin n → E) v (i + 1) ((σ : Fin n → E) i) := by
    intro v
    unfold codeMap
    exact codePrefix_stable μ (σ : Fin n → E) σ.injective v (i + 1) n i.2
      ((σ : Fin n → E) i)
      (by rw [mem_prefixSet_iff]; exact ⟨i, Nat.lt_succ_self _, rfl⟩)
  rw [hstab w, hstab w']
  
  have hi1k : i + 1 ≤ k := by omega
  rw [codePrefix_congr_of_agree μ (σ : Fin n → E) w w' (i + 1) (by omega)
    (fun j hj => hagree j (by omega))]












theorem f_adapt_zero_eq {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (U V : Fin n → ℝ) :
    f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) 0))
      = f (codeMap μ (σ : Fin n → E) U) := by
  set m := stopVal μ σ f U with hm
  rw [adaptWt_zero]
  
  have hagree : ∀ i : Fin n, (i : ℕ) < m → (mixUV U V m) i = U i := by
    intro i hi; unfold mixUV; simp [hi]
  
  have hpref : ∀ e ∈ prefixSet (σ : Fin n → E) m,
      codeMap μ (σ : Fin n → E) (mixUV U V m) e = codeMap μ (σ : Fin n → E) U e :=
    codeMap_agree_on_prefix μ σ (mixUV U V m) U m hagree
  
  exact stopVal_determines μ σ f U (codeMap μ (σ : Fin n → E) (mixUV U V m)) hpref




theorem adapt_step_eq_of_gt_stop {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (U V : Fin n → ℝ) (t : ℕ) (ht : stopVal μ σ f U < t) :
    codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t)
      = codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t - 1)) := by
  set m := stopVal μ σ f U with hm
  rw [adaptWt_ge_stop U V m t (by omega), adaptWt_ge_stop U V m (t - 1) (by omega)]










lemma measurable_stopVal (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) :
    Measurable (fun U : Fin n → ℝ => stopVal μ σ f U) := by
  have : (fun U : Fin n → ℝ => stopVal μ σ f U)
      = (fun X => stopValC σ f X) ∘ (fun U => codeMap μ (σ : Fin n → E) U) := rfl
  rw [this]
  exact (measurable_of_countable _).comp (measurable_codeMap μ σ)



lemma measurable_mixUV {n : ℕ} (m : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => mixUV p.1 p.2 m) := by
  apply measurable_pi_lambda
  intro i; unfold mixUV
  by_cases h : (i : ℕ) < m
  · simp only [h, if_true]; exact (measurable_pi_apply i).comp measurable_fst
  · simp only [h, if_false]; exact (measurable_pi_apply i).comp measurable_snd



lemma measurable_adaptWt_fixed {n : ℕ} (m s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => adaptWt p.1 p.2 m s) := by
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => adaptWt p.1 p.2 m s)
      = (fun p => Wt (mixUV p.1 p.2 m) p.2 s) := by
    funext p; rw [adaptWt_eq_Wt_mix]
  rw [hrw]
  apply measurable_pi_lambda
  intro i; unfold Wt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h, if_false]
    exact (measurable_pi_apply i).comp (measurable_mixUV m)




lemma measurable_g_adaptWt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) (s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))) := by
  
  have hstop : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => stopVal μ σ f p.1) :=
    (measurable_stopVal μ σ f).comp measurable_fst
  
  
  have key : ∀ m : ℕ, Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) :=
    fun m => (measurable_g_codeMap μ σ g).comp (measurable_adaptWt_fixed m s)
  
  have hglue : Measurable (fun mp : ℕ × ((Fin n → ℝ) × (Fin n → ℝ)) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt mp.2.1 mp.2.2 mp.1 s))) :=
    measurable_from_prod_countable_right key
  exact hglue.comp (hstop.prodMk measurable_id)
















theorem var_le_adapt_first_step {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0))
            - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))|
            ∂((Vcube n).prod (Vcube n)) := by
  
  have hpt : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))|)
      = (fun p => |f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 0))
          - f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 n))|) := by
    funext p
    rw [f_adapt_zero_eq (μ := μ) (f := f) σ p.1 p.2, adaptWt_card, Wt_zero, Wt_card]
  rw [hpt]
  exact var_le_grandCoupling_first_step hpos hμ1 σ hf0 hf1










noncomputable def truncInd (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : ℝ :=
  if t ≤ stopVal μ σ f U then (1 : ℝ) else 0


lemma truncInd_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : |truncInd μ σ f U t| ≤ 1 := by
  unfold truncInd; split <;> norm_num


lemma measurable_truncInd (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    Measurable (fun U : Fin n → ℝ => truncInd μ σ f U t) := by
  unfold truncInd
  exact Measurable.ite (measurableSet_le measurable_const (measurable_stopVal μ σ f))
    measurable_const measurable_const





lemma abs_adapt_step_eq_mul_truncInd {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (U V : Fin n → ℝ) (t : ℕ) :
    |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t + 1)))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))|
      = |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t + 1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))|
        * truncInd μ σ f U (t + 1) := by
  unfold truncInd
  by_cases ht : t + 1 ≤ stopVal μ σ f U
  · rw [if_pos ht, mul_one]
  · 
    rw [if_neg ht, mul_zero]
    have hgt : stopVal μ σ f U < t + 1 := by omega
    have heq := adapt_step_eq_of_gt_stop σ U V (t + 1) hgt
    simp only [Nat.add_sub_cancel] at heq
    rw [heq, sub_self, abs_zero]



lemma integrable_abs_adapt_step (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (s₁ s₂ : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))|)
      ((Vcube n).prod (Vcube n)) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  refine StatMech.Probability.ContinuousFKG.integrable_of_bdd _
    (((measurable_g_adaptWt μ σ f f s₁).sub (measurable_g_adaptWt μ σ f f s₂)).abs)
    (C := 2*Cf) (fun p => ?_)
  rw [abs_abs]
  calc |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))|
      ≤ |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁))|
        + |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))| := abs_sub _ _
    _ ≤ 2*Cf := by linarith [hfC (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₁)),
                              hfC (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s₂))]


lemma integrable_abs_adapt_step_trunc (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (t : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
        * truncInd μ σ f p.1 (t + 1))
      ((Vcube n).prod (Vcube n)) := by
  
  have hpt : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
        * truncInd μ σ f p.1 (t + 1))
      = (fun p => |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|) := by
    funext p; rw [← abs_adapt_step_eq_mul_truncInd σ p.1 p.2 t]
  rw [hpt]
  exact integrable_abs_adapt_step μ σ hfC (t+1) t










theorem trunc_telescope {μ : ConfigSpace E → ℝ} {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) :
    (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) 0))
            - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) n))|
            ∂((Vcube n).prod (Vcube n)))
      ≤ ∑ t ∈ Finset.range n,
          ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                * truncInd μ σ f p.1 (t + 1)
            ∂((Vcube n).prod (Vcube n)) := by
  rw [← integral_finsetSum (Finset.range n)
    (fun t _ => integrable_abs_adapt_step_trunc μ σ hfC t)]
  apply integral_mono (integrable_abs_adapt_step μ σ hfC 0 n)
  · apply integrable_finsetSum; intro t _; exact integrable_abs_adapt_step_trunc μ σ hfC t
  · intro p
    set F : ℕ → ℝ := fun s => f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s)) with hF
    show |F 0 - F n| ≤ ∑ t ∈ Finset.range n,
        |F (t+1) - F t| * truncInd μ σ f p.1 (t + 1)
    
    have hcollapse : ∀ t, |F (t+1) - F t| * truncInd μ σ f p.1 (t + 1) = |F (t+1) - F t| := by
      intro t; rw [← abs_adapt_step_eq_mul_truncInd σ p.1 p.2 t]
    simp_rw [hcollapse]
    have htel : F 0 - F n = ∑ t ∈ Finset.range n, (F t - F (t+1)) := by
      rw [Finset.sum_range_sub' F n]
    rw [htel]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply Finset.sum_congr rfl; intro t _; rw [abs_sub_comm]

























theorem var_le_trunc_telescope {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var μ f
      ≤ (1/2) * ∑ t ∈ Finset.range n,
          ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                * truncInd μ σ f p.1 (t + 1)
            ∂((Vcube n).prod (Vcube n)) := by
  have hf0' : ∀ ω, (0:ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  refine (var_le_adapt_first_step hpos hμ1 σ hf0 hf1).trans ?_
  exact mul_le_mul_of_nonneg_left (trunc_telescope σ hfC) (by norm_num : (0:ℝ) ≤ 1/2)














noncomputable def revealAdapt (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) : ℝ :=
  ∫ p, truncInd μ σ f p.1 ((σ.symm e : ℕ) + 1) ∂((Vcube n).prod (Vcube n))



lemma integrable_truncInd (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => truncInd μ σ f p.1 t)
      ((Vcube n).prod (Vcube n)) :=
  StatMech.Probability.ContinuousFKG.integrable_of_bdd _
    ((measurable_truncInd μ σ f t).comp measurable_fst) (C := 1)
    (fun p => truncInd_le_one μ σ f p.1 t)

























def AdaptStepCovBound (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (htn : t < n),
    (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
          * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)))
      ≤ 2 * (Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩))
          * ∫ p, truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)))
















lemma integral_truncInd_eq_reveal (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (i : Fin n) :
    (∫ p, truncInd μ σ f p.1 ((i : ℕ) + 1) ∂((Vcube n).prod (Vcube n)))
      = revealAdapt μ σ f ((σ : Fin n → E) i) := by
  unfold revealAdapt
  rw [Equiv.symm_apply_apply]












theorem tree_osss_sharp_unconditional {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) (hStep : AdaptStepCovBound μ σ f) :
    Lindeberg.var μ f
      ≤ ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) := by
  
  refine (var_le_trunc_telescope hpos hμ1 σ hf0 hf1).trans ?_
  
  rw [Finset.mul_sum]
  
  have hstepbnd : ∀ i : Fin n,
      (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
              * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n))
        ≤ revealAdapt μ σ f ((σ : Fin n → E) i)
            * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) := by
    intro i
    have hb := hStep (i : ℕ) i.2
    have hi : (⟨(i:ℕ), i.2⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hb
    rw [integral_truncInd_eq_reveal μ σ f i] at hb
    
    have : (1/2 : ℝ) * (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
              * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n)))
        ≤ (1/2) * (2 * (Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i))
            * revealAdapt μ σ f ((σ : Fin n → E) i))) :=
      mul_le_mul_of_nonneg_left hb (by norm_num)
    calc (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
              - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
              * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n))
        ≤ (1/2) * (2 * (Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i))
            * revealAdapt μ σ f ((σ : Fin n → E) i))) := this
      _ = revealAdapt μ σ f ((σ : Fin n → E) i)
            * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) := by ring
  calc ∑ t ∈ Finset.range n,
        (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n))
      = ∑ i : Fin n,
          (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) ((i:ℕ)+1)))
                  - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (i:ℕ)))|
                  * truncInd μ σ f p.1 ((i:ℕ) + 1) ∂((Vcube n).prod (Vcube n)) := by
        rw [Finset.sum_range (fun t =>
          (1/2) * ∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
                  - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
                  * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)))]
    _ ≤ ∑ i : Fin n, revealAdapt μ σ f ((σ : Fin n → E) i)
            * Lindeberg.cov μ f (Lindeberg.coord ((σ : Fin n → E) i)) :=
        Finset.sum_le_sum (fun i _ => hstepbnd i)
    _ = ∑ e, revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e) :=
        Equiv.sum_comp σ (fun e => revealAdapt μ σ f e * Lindeberg.cov μ f (Lindeberg.coord e))










section FK

open StatMech.OSSS.MonotonicFK











theorem fk_q2_osss_sharp_unconditional {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hStep : AdaptStepCovBound (fkMass G p 2) σ f) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, revealAdapt (fkMass G p 2) σ f e
          * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  tree_osss_sharp_unconditional
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num)) σ hf0 hf1 hStep

end FK

end AdaptMConditional

end OSSS

end StatMech
