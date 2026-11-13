/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Code.OSSS.UBlockFactor

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]











lemma acp_detAtC_congr_of_codeMap_agree {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ)
    (X X' : ConfigSpace E) (m : ℕ)
    (hpref : ∀ e ∈ prefixSet σ m, X e = X' e) :
    detAtC σ f X m ↔ detAtC σ f X' m := by
  have hfXX' : detAtC σ f X m → f X = f X' := fun hdet =>
    (hdet X' (fun e he => (hpref e he).symm)).symm
  unfold detAtC
  constructor
  · intro hdet w hw
    have hwX : ∀ e ∈ prefixSet σ m, w e = X e := fun e he => by rw [hw e he, ← hpref e he]
    rw [hdet w hwX]; exact hfXX' hdet
  · intro hdet w hw
    have hfX'X : f X' = f X := by
      have hdet' : detAtC σ f X' m := hdet
      exact (hdet' X (fun e he => hpref e he)).symm
    have hwX' : ∀ e ∈ prefixSet σ m, w e = X' e := fun e he => by rw [hw e he, hpref e he]
    rw [hdet w hwX']; exact hfX'X



lemma acp_stopVal_gt_congr (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U U' : Fin n → ℝ) (t : ℕ)
    (hagree : ∀ i : Fin n, (i : ℕ) < t → U i = U' i) :
    (t + 1 ≤ stopVal μ σ f U) ↔ (t + 1 ≤ stopVal μ σ f U') := by
  unfold stopVal stopValC
  rw [Nat.le_find_iff, Nat.le_find_iff]
  constructor <;> intro h m hm <;> rw [Nat.lt_succ_iff] at hm
  · intro hdet'
    refine h m (by omega) ?_
    refine (acp_detAtC_congr_of_codeMap_agree (σ : Fin n → E) f _ _ m ?_).mpr hdet'
    exact codeMap_agree_on_prefix μ σ U U' m (fun i hi => hagree i (by omega))
  · intro hdet
    refine h m (by omega) ?_
    refine (acp_detAtC_congr_of_codeMap_agree (σ : Fin n → E) f _ _ m ?_).mpr hdet
    exact codeMap_agree_on_prefix μ σ U' U m (fun i hi => (hagree i (by omega)).symm)




noncomputable def acp_truncHead (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) : ℝ :=
  truncInd μ σ f ((ubfSplit n t).symm (A, fun _ => 0)) (t + 1)




lemma acp_truncInd_factors (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (U : Fin n → ℝ) :
    truncInd μ σ f U (t + 1) = acp_truncHead μ σ f t (((ubfSplit n t) U).1) := by
  unfold acp_truncHead truncInd
  
  have hagree : ∀ i : Fin n, (i : ℕ) < t →
      U i = ((ubfSplit n t).symm ((((ubfSplit n t) U).1), fun _ => 0)) i := by
    intro i hi
    show U i = (if h : (i : ℕ) < t then ((ubfSplit n t) U).1 ⟨i, h⟩
                else (fun _ : {j : Fin n // ¬ (j : ℕ) < t} => (0:ℝ)) ⟨i, h⟩)
    rw [dif_pos hi]; rfl
  exact if_congr (acp_stopVal_gt_congr μ σ f U _ t hagree) rfl rfl


lemma acp_measurable_truncHead (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) :
    Measurable (acp_truncHead μ σ f t) := by
  unfold acp_truncHead
  refine (measurable_truncInd μ σ f (t + 1)).comp ?_
  exact (ubfSplit n t).symm.measurable.comp (measurable_id.prodMk measurable_const)


lemma acp_truncHead_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    |acp_truncHead μ σ f t A| ≤ 1 := truncInd_le_one μ σ f _ (t + 1)











lemma acp_measurable_fiberDiag (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (e : E) (s : ℕ) :
    Measurable (fun U : Fin n → ℝ => fiberDiag μ σ f e s U) := by
  have hjoint : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))) :=
    (measurable_g_adaptWt μ σ f f s).mul (measurable_g_adaptWt μ σ f (Lindeberg.coord e) s)
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable


lemma acp_fiberDiag_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (s : ℕ) (U : Fin n → ℝ) :
    |fiberDiag μ σ f e s U| ≤ 1 := by
  unfold fiberDiag
  calc |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))
          * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)|
      ≤ ∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))
          * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) := by
        refine integral_mono ?_ (integrable_const 1) (fun V => ?_)
        · exact (adsD_integrable_prod_obs_fiber μ σ hfC e U (stopVal μ σ f U) s s).abs
        · rw [abs_mul, ← one_mul (1:ℝ)]
          exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num)
    _ = 1 := by simp


lemma acp_measurable_fiberCross_marg_f (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (s : ℕ) :
    Measurable (fun U : Fin n → ℝ =>
      ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)) :=
  (measurable_g_adaptWt μ σ f f s).stronglyMeasurable.integral_prod_right'.measurable

lemma acp_measurable_fiberCross_marg_c (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (e : E) (s : ℕ) :
    Measurable (fun U : Fin n → ℝ =>
      ∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)) :=
  (measurable_g_adaptWt μ σ f (Lindeberg.coord e) s).stronglyMeasurable.integral_prod_right'.measurable


lemma acp_measurable_fiberCross (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (e : E) (s₁ s₂ : ℕ) :
    Measurable (fun U : Fin n → ℝ => fiberCross μ σ f e s₁ s₂ U) := by
  unfold fiberCross
  exact (acp_measurable_fiberCross_marg_f μ σ s₁).mul (acp_measurable_fiberCross_marg_c μ σ e s₂)


lemma acp_fiberCross_marg_f_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (s : ℕ) (U : Fin n → ℝ) :
    |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)| ≤ 1 := by
  calc |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)|
      ≤ ∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) :=
        integral_mono (ContinuousFKG.integrable_of_bdd _
          ((adsD_measurable_f_adaptWt_fiber μ σ f U (stopVal μ σ f U) s).abs)
          (fun V => by rw [abs_abs]; exact hfC _))
          (integrable_const 1) (fun V => hfC _)
    _ = 1 := by simp


lemma acp_fiberCross_marg_c_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (e : E) (s : ℕ) (U : Fin n → ℝ) :
    |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)| ≤ 1 := by
  calc |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)|
      ≤ ∫ V, |Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) :=
        integral_mono (ContinuousFKG.integrable_of_bdd _
          ((adsD_measurable_f_adaptWt_fiber μ σ (Lindeberg.coord e) U (stopVal μ σ f U) s).abs)
          (fun V => by rw [abs_abs]; exact GrandCoupling.abs_coord_le_one e _))
          (integrable_const 1) (fun V => GrandCoupling.abs_coord_le_one e _)
    _ = 1 := by simp


lemma acp_fiberCross_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (s₁ s₂ : ℕ) (U : Fin n → ℝ) :
    |fiberCross μ σ f e s₁ s₂ U| ≤ 1 := by
  unfold fiberCross
  rw [abs_mul, ← one_mul (1:ℝ)]
  exact mul_le_mul (acp_fiberCross_marg_f_le_one μ σ hfC s₁ U)
    (acp_fiberCross_marg_c_le_one μ σ e s₂ U) (abs_nonneg _) (by norm_num)















noncomputable def acp_join {n : ℕ} (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) : Fin n → ℝ :=
  (ubfSplit n t).symm (A, B)











def acp_TailCondLaw (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Prop :=
  ∀ (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
    let e := (σ : Fin n → E) ⟨t, htn⟩
    ((∫ B, fiberDiag μ σ f e t (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ ((∫ B, fiberDiag μ σ f e (t+1) (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, fiberCross μ σ f e t (t+1) (acp_join t A B) ∂(ubfTail n t))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, fiberCross μ σ f e (t+1) t (acp_join t A B) ∂(ubfTail n t))

end AdaptDisintegration

end OSSS

end StatMech
