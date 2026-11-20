/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/































































import Code.OSSS.TailSelMPClose

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














theorem sp1_map_uncurry_const {γ α β : Type*} [MeasurableSpace γ] [MeasurableSpace α]
    [MeasurableSpace β] (κ : Measure γ) [IsProbabilityMeasure κ] (ν : Measure α)
    [SigmaFinite ν] {G : γ → α → β} (hG : Measurable (Function.uncurry G)) {ξ : Measure β}
    (hcol : ∀ c, Measure.map (G c) ν = ξ) :
    Measure.map (Function.uncurry G) (κ.prod ν) = ξ := by
  ext T hT
  rw [Measure.map_apply hG hT, Measure.prod_apply (hG hT)]
  have hGc : ∀ c, Measurable (G c) := fun c => hG.comp (measurable_const.prodMk measurable_id)
  have hpt : ∀ c, ν (Prod.mk c ⁻¹' (Function.uncurry G ⁻¹' T)) = ξ T := by
    intro c
    have hset : Prod.mk c ⁻¹' (Function.uncurry G ⁻¹' T) = (G c) ⁻¹' T := by
      ext a; simp [Function.uncurry]
    rw [hset, ← Measure.map_apply (hGc c) hT, hcol c]
  simp_rw [hpt]
  rw [MeasureTheory.lintegral_const, measure_univ, mul_one]












abbrev sp1_Sing (n t : ℕ) :=
  {j : {i : Fin n // ¬ (i:ℕ) < t} // ¬ ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1}




def sp1_idxEq (n t : ℕ) :
    {j : {i : Fin n // ¬ (i:ℕ) < t} // ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1}
      ≃ {i : Fin n // ¬ (i:ℕ) < t+1} where
  toFun := fun j => ⟨(j.1 : Fin n), j.2⟩
  invFun := fun i => ⟨⟨(i : Fin n), by have := i.2; omega⟩, i.2⟩
  left_inv := by intro j; rfl
  right_inv := by intro i; rfl


noncomputable def sp1_renTail (n t : ℕ) :
    ({j : {i : Fin n // ¬ (i:ℕ) < t} // ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1} → ℝ)
      ≃ᵐ ({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // ¬ (i:ℕ) < t+1} => ℝ) (sp1_idxEq n t)




noncomputable def sp1_tailDisint (n t : ℕ) :
    ({i : Fin n // ¬ (i:ℕ) < t} → ℝ) ≃ᵐ
      (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {i : Fin n // ¬ (i:ℕ) < t} => ℝ)
      (fun j => ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1)).trans
    (MeasurableEquiv.prodCongr (sp1_renTail n t) (MeasurableEquiv.refl (sp1_Sing n t → ℝ)))

instance (n t : ℕ) : IsProbabilityMeasure
    (Measure.pi (fun _ : sp1_Sing n t => unitMeasure)) := by infer_instance





theorem sp1_tailSplit_mp (n t : ℕ) :
    MeasurePreserving (sp1_tailDisint n t) (ubfTail n t)
      ((ubfTail n (t+1)).prod (Measure.pi (fun _ : sp1_Sing n t => unitMeasure))) := by
  unfold sp1_tailDisint
  
  have hsplit : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {i : Fin n // ¬ (i:ℕ) < t} => ℝ)
        (fun j => ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1))
      (ubfTail n t)
      ((Measure.pi (fun _ => unitMeasure)).prod (Measure.pi fun _ => unitMeasure)) := by
    show MeasurePreserving _ (Measure.pi (fun _ => unitMeasure)) _
    exact measurePreserving_piEquivPiSubtypeProd _ _
  
  have hren : MeasurePreserving (sp1_renTail n t)
      (Measure.pi (fun _ => unitMeasure)) (ubfTail n (t+1)) := by
    show MeasurePreserving _ _ (Measure.pi (fun _ => unitMeasure))
    exact measurePreserving_piCongrLeft (fun _ => unitMeasure) (sp1_idxEq n t)
  have hprod := hren.prod
    (MeasurePreserving.id (Measure.pi (fun _ : sp1_Sing n t => unitMeasure)))
  exact (show MeasurePreserving
      (MeasurableEquiv.prodCongr (sp1_renTail n t) (MeasurableEquiv.refl (sp1_Sing n t → ℝ)))
      _ _ from hprod).comp hsplit





noncomputable def sp1_headExtC {n : ℕ} (t : ℕ) (htn : t < n)
    (A : {i : Fin n // (i:ℕ) < t} → ℝ) (c : sp1_Sing n t → ℝ) :
    {i : Fin n // (i:ℕ) < t+1} → ℝ :=
  fun i => if h : (i:ℕ) < t then A ⟨i, h⟩ else c ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩


lemma sp1_headExtC_meas {n : ℕ} (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    Measurable (fun c : sp1_Sing n t → ℝ => sp1_headExtC t htn A c) := by
  refine measurable_pi_lambda (fun (c : sp1_Sing n t → ℝ) => sp1_headExtC t htn A c)
    (fun i => ?_)
  unfold sp1_headExtC
  by_cases h : (i:ℕ) < t
  · simp only [h, dif_pos]; exact measurable_const
  · simp only [h, dif_neg, not_false_iff]; exact measurable_pi_apply _





lemma sp1_acp_join_compat {n : ℕ} (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i:ℕ) < t} → ℝ) :
    acp_join t A B
      = acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2))
          ((sp1_tailDisint n t B).1) := by
  have h2 : (sp1_tailDisint n t B).2 ⟨⟨⟨t, htn⟩, by simp⟩, by simp⟩ = B ⟨⟨t, htn⟩, by simp⟩ := by
    unfold sp1_tailDisint
    show ((MeasurableEquiv.prodCongr (sp1_renTail n t) (MeasurableEquiv.refl (sp1_Sing n t → ℝ)))
      ((MeasurableEquiv.piEquivPiSubtypeProd _ _) B)).2 _ = _
    rfl
  funext i
  by_cases hit : (i:ℕ) < t
  · rw [tsc_acp_join_head t A B i hit, tsc_acp_join_head (t+1) _ _ i (by omega)]
    unfold sp1_headExtC; simp [hit]
  · by_cases hit1 : (i:ℕ) < t+1
    · have hieq : (i:ℕ) = t := by omega
      rw [tsc_acp_join_tail t A B i hit, tsc_acp_join_head (t+1) _ _ i hit1]
      unfold sp1_headExtC; simp only [hit, dif_neg, not_false_iff]
      rw [h2]; congr 1; apply Subtype.ext; apply Fin.ext; exact hieq
    · rw [tsc_acp_join_tail t A B i hit, tsc_acp_join_tail (t+1) _ _ i hit1]
      show B _ = (sp1_tailDisint n t B).1 _
      unfold sp1_tailDisint sp1_renTail; rfl



noncomputable def sp1_G (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) (c : sp1_Sing n t → ℝ) :
    (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
  atl_selRand μ σ f (t+1) (t+1) (sp1_headExtC t htn A c)



noncomputable def sp1_reshuf {n : ℕ} (t : ℕ)
    (p : ({i : Fin n // ¬ (i:ℕ) < t} → ℝ) × (Fin n → ℝ)) :
    (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) :=
  ((sp1_tailDisint n t p.1).2, ((sp1_tailDisint n t p.1).1, p.2))




theorem sp1_reshuf_mp {n : ℕ} (t : ℕ) :
    MeasurePreserving (sp1_reshuf (n := n) t) ((ubfTail n t).prod (Vcube n))
      ((Measure.pi (fun _ : sp1_Sing n t => unitMeasure)).prod
        ((ubfTail n (t+1)).prod (Vcube n))) := by
  set κ := Measure.pi (fun _ : sp1_Sing n t => unitMeasure) with hκ
  
  have hstep1 : MeasurePreserving (Prod.map (sp1_tailDisint n t) (id : (Fin n → ℝ) → _))
      ((ubfTail n t).prod (Vcube n)) (((ubfTail n (t+1)).prod κ).prod (Vcube n)) :=
    (sp1_tailSplit_mp n t).prod (MeasurePreserving.id (Vcube n))
  
  have hswap : MeasurePreserving
      (Prod.swap : (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) → _)
      ((ubfTail n (t+1)).prod κ) (κ.prod (ubfTail n (t+1))) :=
    Measure.measurePreserving_swap
  have hstep2 : MeasurePreserving
      (Prod.map (Prod.swap : (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) → _)
        (id : (Fin n → ℝ) → _))
      (((ubfTail n (t+1)).prod κ).prod (Vcube n)) ((κ.prod (ubfTail n (t+1))).prod (Vcube n)) :=
    hswap.prod (MeasurePreserving.id (Vcube n))
  
  have hstep3 : MeasurePreserving
      (MeasurableEquiv.prodAssoc :
        ((sp1_Sing n t → ℝ) × ({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ)) × (Fin n → ℝ) ≃ᵐ _)
      ((κ.prod (ubfTail n (t+1))).prod (Vcube n)) (κ.prod ((ubfTail n (t+1)).prod (Vcube n))) :=
    measurePreserving_prodAssoc κ (ubfTail n (t+1)) (Vcube n)
  have hcomp := (hstep3.comp hstep2).comp hstep1
  
  have heq : ((⇑MeasurableEquiv.prodAssoc) ∘
      (Prod.map (Prod.swap : (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) → _)
        (id : (Fin n → ℝ) → _))) ∘
      (Prod.map (sp1_tailDisint n t) (id : (Fin n → ℝ) → _)) = sp1_reshuf (n := n) t := by
    funext p; rfl
  rw [heq] at hcomp
  exact hcomp


lemma sp1_reshuf_meas {n : ℕ} (t : ℕ) : Measurable (sp1_reshuf (n := n) t) :=
  (sp1_reshuf_mp t).measurable







theorem sp1_selRand_factor (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    atl_selRand μ σ f t (t+1) A
      = (Function.uncurry (sp1_G μ σ f t htn A)) ∘ (sp1_reshuf (n := n) t) := by
  funext p
  obtain ⟨B, V⟩ := p
  show adaptWt (acp_join t A B) V (stopVal μ σ f (acp_join t A B)) (t+1)
      = adaptWt (acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2)) ((sp1_tailDisint n t B).1)) V
          (stopVal μ σ f (acp_join (t+1) (sp1_headExtC t htn A ((sp1_tailDisint n t B).2)) ((sp1_tailDisint n t B).1))) (t+1)
  rw [sp1_acp_join_compat t htn A B]


lemma sp1_G_uncurry_meas (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    Measurable (Function.uncurry (sp1_G μ σ f t htn A)) := by
  
  
  set Hd : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
    fun q => acp_join (t+1) (sp1_headExtC t htn A q.1) q.2.1 with hHd
  have hHdm : Measurable Hd := by
    show Measurable (fun q : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) =>
      (ubfSplit n (t+1)).symm (sp1_headExtC t htn A q.1, q.2.1))
    exact (ubfSplit n (t+1)).symm.measurable.comp
      (((sp1_headExtC_meas t htn A).comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd))
  
  have hstop : Measurable (fun q => stopVal μ σ f (Hd q)) :=
    (measurable_stopVal μ σ f).comp hHdm
  
  have hV : Measurable (fun q : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) =>
      q.2.2) := measurable_snd.comp measurable_snd
  
  have key : ∀ m : ℕ, Measurable (fun q : (sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ)) =>
      adaptWt (Hd q) (q.2.2) m (t+1)) :=
    fun m => (measurable_adaptWt_fixed m (t+1)).comp (hHdm.prodMk hV)
  have hglue : Measurable (fun mq : ℕ × ((sp1_Sing n t → ℝ) × (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (Fin n → ℝ))) =>
      adaptWt (Hd mq.2) (mq.2.2.2) mq.1 (t+1)) :=
    measurable_from_prod_countable_right key
  exact hglue.comp (hstop.prodMk measurable_id)









theorem sp1_tailSelMP (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    atl_TailSelMP μ σ f t (t+1) A := by
  show MeasurePreserving (atl_selRand μ σ f t (t+1) A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  refine ⟨tsm_measurable_selRand μ σ f t (t+1) A, ?_⟩
  rw [sp1_selRand_factor μ σ f t htn A,
    ← Measure.map_map (sp1_G_uncurry_meas μ σ f t htn A) (sp1_reshuf_meas t),
    (sp1_reshuf_mp t).map_eq]
  
  
  exact sp1_map_uncurry_const _ _ (sp1_G_uncurry_meas μ σ f t htn A)
    (fun c => (tsc_tailSelMP_at_s_eq_t μ σ f (t+1) (sp1_headExtC t htn A c)).map_eq)


















theorem sp1_restrictedSum_of_tailSelMP (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t s : ℕ) (A : {i : Fin n // (i:ℕ) < t} → ℝ)
    (hMP : atl_TailSelMP μ σ f t s A) :
    tsm_TailSelMP_restrictedSum μ σ f t s A := by
  show (Measure.sum (fun k => Measure.map (osp_tailSelFixed t s k A)
      (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)))) = Vcube n
  
  have hpiece : ∀ k, Measure.map (osp_tailSelFixed t s k A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k))
      = Measure.map (atl_selRand μ σ f t s A)
        (((ubfTail n t).prod (Vcube n)).restrict (tsm_switchPiece μ σ f t A k)) := by
    intro k
    refine tsm_map_restrict_congr ((ubfTail n t).prod (Vcube n)) (tsm_switchPiece μ σ f t A k)
      (osp_tailSelFixed_meas t s k A) (tsm_measurable_selRand μ σ f t s A) ?_
    intro p hp
    exact (tsm_selRand_eq_on_piece μ σ f t s A k p hp).symm
  simp_rw [hpiece]
  rw [← Measure.map_sum (tsm_measurable_selRand μ σ f t s A).aemeasurable,
    ← Measure.restrict_iUnion (tsm_switchPiece_disj μ σ f t A) (tsm_switchPiece_meas μ σ f t A),
    tsm_switchPiece_cover μ σ f t A, Measure.restrict_univ]
  exact hMP.map_eq









theorem sp1_restrictedSum_at_s_eq_t_succ (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (htn : t < n) (A : {i : Fin n // (i:ℕ) < t} → ℝ) :
    tsm_TailSelMP_restrictedSum μ σ f t (t+1) A :=
  sp1_restrictedSum_of_tailSelMP μ σ f t (t+1) A (sp1_tailSelMP μ σ f t htn A)

end AdaptDisintegration

end OSSS

end StatMech
