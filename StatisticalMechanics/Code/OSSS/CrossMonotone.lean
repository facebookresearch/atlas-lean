/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Code.OSSS.CrossVFKG

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]









lemma cmn_detAtC_prefix_local {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ)
    (X X' : ConfigSpace E) (t : ℕ) (hagree : ∀ e ∈ prefixSet σ t, X e = X' e) :
    detAtC σ f X t ↔ detAtC σ f X' t :=
  ⟨tsc_detAtC_transport σ f X X' t hagree t (le_refl t),
   tsc_detAtC_transport σ f X' X t (fun e he => (hagree e he).symm) t (le_refl t)⟩


lemma cmn_detAtC_mono {n : ℕ} (σ : Fin n → E) (f : ConfigSpace E → ℝ) (X : ConfigSpace E)
    {j k : ℕ} (hjk : j ≤ k) (hdet : detAtC σ f X j) : detAtC σ f X k := by
  intro w hw
  exact hdet w (fun e he => hw e (tsc_prefixSet_mono σ hjk he))


lemma cmn_stopValC_le_iff {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (X : ConfigSpace E)
    (t : ℕ) : stopValC σ f X ≤ t ↔ detAtC (σ : Fin n → E) f X t := by
  unfold stopValC
  rw [Nat.find_le_iff]
  constructor
  · rintro ⟨j, hjt, hdet⟩; exact cmn_detAtC_mono (σ : Fin n → E) f X hjt hdet
  · intro hdet; exact ⟨t, le_refl t, hdet⟩





lemma cmn_stop_lt_const_in_tail (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    (t < stopVal μ σ f (acp_join t A B)) ↔ (t < stopVal μ σ f (acp_join t A B')) := by
  have hagree : ∀ e ∈ prefixSet (σ : Fin n → E) t,
      codeMap μ (σ : Fin n → E) (acp_join t A B) e
        = codeMap μ (σ : Fin n → E) (acp_join t A B') e := by
    apply codeMap_agree_on_prefix μ σ
    intro i hi
    rw [tsc_acp_join_head t A B i hi, tsc_acp_join_head t A B' i hi]
  have hdet : detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) (acp_join t A B)) t
      ↔ detAtC (σ : Fin n → E) f (codeMap μ (σ : Fin n → E) (acp_join t A B')) t :=
    cmn_detAtC_prefix_local (σ : Fin n → E) f _ _ t hagree
  rw [stopVal_eq_stopValC, stopVal_eq_stopValC, ← not_le, ← not_le,
    cmn_stopValC_le_iff σ f _ t, cmn_stopValC_le_iff σ f _ t, hdet]












lemma cmn_coord_bit_local (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
    (hbt : B ⟨⟨t, htn⟩, by simp⟩ = B' ⟨⟨t, htn⟩, by simp⟩) (V : Fin n → ℝ) :
    codeMap μ (σ : Fin n → E)
        (adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) t)
        ((σ : Fin n → E) ⟨t, htn⟩)
      = codeMap μ (σ : Fin n → E)
        (adaptWt (acp_join t A B') V (stopVal μ σ f (acp_join t A B')) t)
        ((σ : Fin n → E) ⟨t, htn⟩) := by
  apply cvf_coord_local μ σ t htn _ _
  intro i hi
  show adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) t i
      = adaptWt (acp_join t A B') V (stopVal μ σ f (acp_join t A B')) t i
  unfold adaptWt
  by_cases hit : (i : ℕ) < t
  · simp only [hit, if_true]
  · 
    have hiet : (i : ℕ) = t := by omega
    simp only [hit, if_false]
    have hjoinB : acp_join t A B i = B ⟨i, hit⟩ := tsc_acp_join_tail t A B i hit
    have hjoinB' : acp_join t A B' i = B' ⟨i, hit⟩ := tsc_acp_join_tail t A B' i hit
    have hieq : (⟨i, hit⟩ : {j : Fin n // ¬ (j : ℕ) < t})
        = ⟨⟨t, htn⟩, by simp⟩ := by
      apply Subtype.ext; apply Fin.ext; exact hiet
    by_cases hτ : (i : ℕ) < stopVal μ σ f (acp_join t A B)
    · 
      have hτ' : (i : ℕ) < stopVal μ σ f (acp_join t A B') := by
        rw [hiet] at hτ ⊢
        exact (cmn_stop_lt_const_in_tail μ σ f t A B B').mp hτ
      simp only [hτ, hτ', if_true, hjoinB, hjoinB', hieq, hbt]
    · 
      have hτ' : ¬ (i : ℕ) < stopVal μ σ f (acp_join t A B') := by
        rw [hiet] at hτ ⊢
        exact fun h => hτ ((cmn_stop_lt_const_in_tail μ σ f t A B B').mpr h)
      simp only [hτ, hτ', if_false]





lemma cmn_M2_local (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B B' : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
    (hbt : B ⟨⟨t, htn⟩, by simp⟩ = B' ⟨⟨t, htn⟩, by simp⟩) :
    atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A B
      = atl_margRand μ σ f (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) t t A B' := by
  unfold atl_margRand
  congr 1
  funext V
  unfold Lindeberg.coord
  rw [cmn_coord_bit_local μ σ f t htn A B B' hbt V]















lemma cmn_disint {n : ℕ} (t : ℕ) {h : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) → ℝ}
    (hmeas : Measurable h) {C : ℝ} (hbdd : ∀ B, |h B| ≤ C) :
    (∫ B, h B ∂(ubfTail n t))
      = ∫ c, (∫ B', h ((sp1_tailDisint n t).symm (B', c))
          ∂(ubfTail n (t+1))) ∂(Measure.pi (fun _ : sp1_Sing n t => unitMeasure)) := by
  set κ := Measure.pi (fun _ : sp1_Sing n t => unitMeasure) with hκ
  
  have hcomp : (∫ B, h B ∂(ubfTail n t))
      = ∫ p, h ((sp1_tailDisint n t).symm p) ∂((ubfTail n (t+1)).prod κ) := by
    rw [← (sp1_tailSplit_mp n t).integral_comp (sp1_tailDisint n t).measurableEmbedding
      (fun p => h ((sp1_tailDisint n t).symm p))]
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B
    simp only [MeasurableEquiv.symm_apply_apply]
  
  have hmeas_p : Measurable (fun p : (({i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) =>
      h ((sp1_tailDisint n t).symm p)) :=
    hmeas.comp (sp1_tailDisint n t).symm.measurable
  have hint : Integrable (fun p => h ((sp1_tailDisint n t).symm p)) ((ubfTail n (t+1)).prod κ) :=
    ContinuousFKG.integrable_of_bdd _ hmeas_p (fun p => hbdd _)
  rw [hcomp, integral_prod_symm _ hint]



lemma cmn_symm_coord_t {n : ℕ} (t : ℕ) (htn : t < n)
    (B' : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) (c : sp1_Sing n t → ℝ) :
    (sp1_tailDisint n t).symm (B', c) ⟨⟨t, htn⟩, by simp⟩ = c ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩ := by
  have hrt : (sp1_tailDisint n t) ((sp1_tailDisint n t).symm (B', c)) = (B', c) :=
    (sp1_tailDisint n t).apply_symm_apply (B', c)
  have h2 : (sp1_tailDisint n t ((sp1_tailDisint n t).symm (B', c))).2
        ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩
      = (sp1_tailDisint n t).symm (B', c) ⟨⟨t, htn⟩, by simp⟩ := by
    unfold sp1_tailDisint
    rfl
  rw [hrt] at h2
  exact h2.symm



lemma cmn_join_reassemble {n : ℕ} (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B' : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) (c : sp1_Sing n t → ℝ) :
    acp_join t A ((sp1_tailDisint n t).symm (B', c))
      = acp_join (t+1) (sp1_headExtC t htn A c) B' := by
  have hrt : (sp1_tailDisint n t) ((sp1_tailDisint n t).symm (B', c)) = (B', c) :=
    (sp1_tailDisint n t).apply_symm_apply (B', c)
  rw [sp1_acp_join_compat t htn A ((sp1_tailDisint n t).symm (B', c)), hrt]



lemma cmn_M1_reassemble (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B' : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ) (c : sp1_Sing n t → ℝ) :
    atl_margRand μ σ f f t (t+1) A ((sp1_tailDisint n t).symm (B', c))
      = atl_margRand μ σ f f (t+1) (t+1) (sp1_headExtC t htn A c) B' := by
  unfold atl_margRand
  rw [cmn_join_reassemble t htn A B' c]

















theorem cmn_cross_pred_eq (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) (htn : t < n)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, fiberCross μ σ f ((σ : Fin n → E) ⟨t, htn⟩) (t+1) t (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord ((σ : Fin n → E) ⟨t, htn⟩)) := by
  classical
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  set M₁ := atl_margRand μ σ f f t (t+1) A with hM₁
  set M₂ := atl_margRand μ σ f (Lindeberg.coord e) t t A with hM₂
  set κ := Measure.pi (fun _ : sp1_Sing n t => unitMeasure) with hκ
  
  have hcrossdef : (∫ B, fiberCross μ σ f e (t+1) t (acp_join t A B) ∂(ubfTail n t))
      = ∫ B, M₁ B * M₂ B ∂(ubfTail n t) := rfl
  
  have hI : (∫ B, M₁ B * M₂ B ∂(ubfTail n t))
      = ∫ c, Lindeberg.mean μ f * M₂ ((sp1_tailDisint n t).symm (0, c)) ∂κ := by
    rw [cmn_disint t (h := fun B => M₁ B * M₂ B)
      ((atl_margRand_meas μ σ f f t (t+1) A).mul (atl_margRand_meas μ σ f (Lindeberg.coord e) t t A))
      (C := 1) (fun B => by
        rw [abs_mul, ← one_mul (1 : ℝ)]
        exact mul_le_mul (atl_margRand_le_one μ σ f f hfC t (t+1) A B)
          (atl_margRand_le_one μ σ f (Lindeberg.coord e)
            (fun ω => GrandCoupling.abs_coord_le_one e ω) t t A B)
          (abs_nonneg _) (by norm_num))]
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro c
    
    have hinner : (∫ B', M₁ ((sp1_tailDisint n t).symm (B', c)) * M₂ ((sp1_tailDisint n t).symm (B', c))
            ∂(ubfTail n (t+1)))
        = ∫ B', atl_margRand μ σ f f (t+1) (t+1) (sp1_headExtC t htn A c) B'
            * M₂ ((sp1_tailDisint n t).symm (0, c)) ∂(ubfTail n (t+1)) := by
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro B'
      show M₁ ((sp1_tailDisint n t).symm (B', c)) * M₂ ((sp1_tailDisint n t).symm (B', c))
        = atl_margRand μ σ f f (t+1) (t+1) (sp1_headExtC t htn A c) B'
            * M₂ ((sp1_tailDisint n t).symm (0, c))
      rw [hM₁, cmn_M1_reassemble μ σ f t htn A B' c]
      congr 1
      
      exact cmn_M2_local μ σ f t htn A _ _ (by
        rw [cmn_symm_coord_t t htn B' c, cmn_symm_coord_t t htn 0 c])
    show (∫ B', M₁ ((sp1_tailDisint n t).symm (B', c)) * M₂ ((sp1_tailDisint n t).symm (B', c))
            ∂(ubfTail n (t+1)))
        = Lindeberg.mean μ f * M₂ ((sp1_tailDisint n t).symm (0, c))
    rw [hinner, integral_mul_const,
      atl_marg_of_MP μ hpos hμ1 σ f hfC (t+1) (t+1) (sp1_headExtC t htn A c)
        (tsc_tailSelMP_at_s_eq_t μ σ f (t+1) (sp1_headExtC t htn A c))]
  
  have hM₂mean : (∫ B, M₂ B ∂(ubfTail n t)) = Lindeberg.mean μ (Lindeberg.coord e) :=
    atl_marg_of_MP μ hpos hμ1 σ (Lindeberg.coord e)
      (fun ω => GrandCoupling.abs_coord_le_one e ω) t t A (tsc_tailSelMP_at_s_eq_t μ σ f t A)
  have hM₂disint : (∫ B, M₂ B ∂(ubfTail n t))
      = ∫ c, M₂ ((sp1_tailDisint n t).symm (0, c)) ∂κ := by
    rw [cmn_disint t (h := M₂) (atl_margRand_meas μ σ f (Lindeberg.coord e) t t A)
      (C := 1) (fun B => atl_margRand_le_one μ σ f (Lindeberg.coord e)
        (fun ω => GrandCoupling.abs_coord_le_one e ω) t t A B)]
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro c
    
    show (∫ B', M₂ ((sp1_tailDisint n t).symm (B', c)) ∂(ubfTail n (t+1)))
        = M₂ ((sp1_tailDisint n t).symm (0, c))
    rw [show (fun B' => M₂ ((sp1_tailDisint n t).symm (B', c)))
          = (fun _ : {i : Fin n // ¬ (i : ℕ) < t+1} → ℝ => M₂ ((sp1_tailDisint n t).symm (0, c)))
        from funext (fun B' => cmn_M2_local μ σ f t htn A _ _ (by
          rw [cmn_symm_coord_t t htn B' c, cmn_symm_coord_t t htn 0 c]))]
    rw [integral_const, show (ubfTail n (t+1)).real Set.univ = 1 from probReal_univ, one_smul]
  
  rw [hcrossdef, hI, integral_const_mul, ← hM₂disint, hM₂mean]












theorem cmn_Cross41 {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) (htn : t < n)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    cvf_Cross41 μ σ f t htn A :=
  le_of_eq (cmn_cross_pred_eq μ hpos hμ1 hmono σ hf hfC t htn A).symm













theorem cmn_tailCondLaw {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) :
    acp_TailCondLaw μ σ f :=
  cvf_tailCondLaw_of_cross41 hpos hμ1 σ hfC
    (fun t htn A => cmn_Cross41 hpos hμ1 hmono σ hf hfC t htn A)

end AdaptDisintegration

end OSSS

end StatMech
