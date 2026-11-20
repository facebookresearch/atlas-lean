/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.OSSS.TailCondLawClose

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



noncomputable def osp_tailSelFixed {n : ℕ} (t s k : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) : Fin n → ℝ :=
  adaptWt (acp_join t A p.1) p.2 k s


lemma osp_tailSelFixed_meas {n : ℕ} (t s k : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (osp_tailSelFixed t s k A) := by
  have hpair : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      (acp_join t A p.1, p.2)) :=
    Measurable.prodMk
      ((ubfSplit n t).symm.measurable.comp (measurable_const.prodMk measurable_fst))
      measurable_snd
  exact (measurable_adaptWt_fixed k s).comp hpair


def osp_proj {n : ℕ} (t : ℕ) :
    ((({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ)) × (Fin n → ℝ))
      → (({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ)) :=
  fun q => (q.1.2, q.2)

lemma osp_proj_meas {n : ℕ} (t : ℕ) : Measurable (osp_proj (n := n) t) :=
  (measurable_snd.comp measurable_fst).prodMk measurable_snd




lemma osp_proj_measurePreserving {n : ℕ} (t : ℕ) :
    MeasurePreserving (osp_proj (n := n) t)
      (((ubfHead n t).prod (ubfTail n t)).prod (Vcube n))
      ((ubfTail n t).prod (Vcube n)) := by
  unfold osp_proj
  have h1 : MeasurePreserving (Prod.snd : (({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ)) → _)
      ((ubfHead n t).prod (ubfTail n t)) (ubfTail n t) := measurePreserving_snd
  exact (h1.prod (MeasurePreserving.id (Vcube n)))















noncomputable def osp_fill {n : ℕ} (t s k : ℕ)
    (q : ((({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ))
            × (Fin n → ℝ))) : Fin n → ℝ :=
  adaptWt (acp_join t q.1.1 q.1.2) q.2 k s




lemma osp_fill_measurePreserving {n : ℕ} (t s k : ℕ) :
    MeasurePreserving (osp_fill (n := n) t s k)
      (((ubfHead n t).prod (ubfTail n t)).prod (Vcube n)) (Vcube n) := by
  
  have hreassemble : MeasurePreserving
      (fun q : ((({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ))
            × (Fin n → ℝ)) => ((ubfSplit n t).symm q.1, q.2))
      (((ubfHead n t).prod (ubfTail n t)).prod (Vcube n))
      ((cube n).prod (Vcube n)) := by
    have hsymm : MeasurePreserving (ubfSplit n t).symm
        ((ubfHead n t).prod (ubfTail n t)) (cube n) :=
      (ubf_pi_block_split n t).symm _
    exact hsymm.prod (MeasurePreserving.id (Vcube n))
  
  have hsel : MeasurePreserving (selMap2 n s k) ((cube n).prod (Vcube n)) (Vcube n) := by
    rw [Vcube_eq_cube]
    exact adsD_selMap2_measurePreserving n s k
  have hcomp := hsel.comp hreassemble
  
  have heq : (selMap2 n s k) ∘ (fun q => ((ubfSplit n t).symm q.1, q.2))
      = osp_fill (n := n) t s k := by
    funext q
    show selMap2 n s k ((ubfSplit n t).symm q.1, q.2) = adaptWt (acp_join t q.1.1 q.1.2) q.2 k s
    rw [adsD_selMap2_eq_adaptWt]
    rfl
  rw [heq] at hcomp
  exact hcomp




lemma osp_fill_eq_tailSel_comp_proj {n : ℕ} (t s k : ℕ) (hts : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    osp_fill (n := n) t s k = (osp_tailSelFixed t s k A) ∘ (osp_proj (n := n) t) := by
  funext q
  show adaptWt (acp_join t q.1.1 q.1.2) q.2 k s = adaptWt (acp_join t A q.1.2) q.2 k s
  exact atc_adaptWt_join_indep_head t s k hts q.1.1 A q.1.2 q.2
















theorem osp_tailSelFixed_mp {n : ℕ} (t s k : ℕ) (hts : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    MeasurePreserving (osp_tailSelFixed t s k A)
      ((ubfTail n t).prod (Vcube n)) (Vcube n) := by
  
  have hfill := osp_fill_measurePreserving (n := n) t s k
  rw [osp_fill_eq_tailSel_comp_proj t s k hts A] at hfill
  
  have hproj := osp_proj_measurePreserving (n := n) t
  refine ⟨osp_tailSelFixed_meas t s k A, ?_⟩
  
  rw [← hproj.map_eq, Measure.map_map (osp_tailSelFixed_meas t s k A) (osp_proj_meas t)]
  exact hfill.map_eq











theorem osp_tailSelFixed_law (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s k : ℕ) (hts : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, (∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V k s)) ∂(Vcube n))
        ∂(ubfTail n t))
      = Lindeberg.mean μ g := by
  have hMP := osp_tailSelFixed_mp t s k hts A
  
  have hjm : Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (osp_tailSelFixed t s k A p))) :=
    (measurable_g_codeMap μ σ g).comp (osp_tailSelFixed_meas t s k A)
  have hint : Integrable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (osp_tailSelFixed t s k A p)))
      ((ubfTail n t).prod (Vcube n)) :=
    ContinuousFKG.integrable_of_bdd _ hjm (fun p => hgC _)
  
  have hfub : (∫ p, g (codeMap μ (σ : Fin n → E) (osp_tailSelFixed t s k A p))
        ∂((ubfTail n t).prod (Vcube n)))
      = ∫ B, (∫ V, g (codeMap μ (σ : Fin n → E)
            (adaptWt (acp_join t A B) V k s)) ∂(Vcube n)) ∂(ubfTail n t) := by
    rw [integral_prod _ hint]; rfl
  
  have hmean : (∫ p, g (codeMap μ (σ : Fin n → E) (osp_tailSelFixed t s k A p))
        ∂((ubfTail n t).prod (Vcube n)))
      = ∑ x, g x * μ x := by
    have hcomp : (∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (osp_tailSelFixed t s k A p)
          ∂((ubfTail n t).prod (Vcube n)))
        = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
      rw [← hMP.map_eq, integral_map hMP.measurable.aemeasurable
        (measurable_g_codeMap μ σ g).aestronglyMeasurable, hMP.map_eq]
    rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]
  rw [← hfub, hmean]; rfl




















theorem osp_tailSelMP_of_const_switch (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (t s : ℕ) (hts : t ≤ s) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (k₀ : ℕ) (hconst : ∀ B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ,
        stopVal μ σ f (acp_join t A B) = k₀) :
    atl_TailSelMP μ σ f t s A := by
  have heq : atl_selRand μ σ f t s A = osp_tailSelFixed t s k₀ A := by
    funext p
    show adaptWt (acp_join t A p.1) p.2 (stopVal μ σ f (acp_join t A p.1)) s
        = adaptWt (acp_join t A p.1) p.2 k₀ s
    rw [hconst p.1]
  show MeasurePreserving (atl_selRand μ σ f t s A) ((ubfTail n t).prod (Vcube n)) (Vcube n)
  rw [heq]
  exact osp_tailSelFixed_mp t s k₀ hts A




















private lemma osp_map_not_count :
    Measure.map (fun b => !b) (Measure.count : Measure Bool) = Measure.count := by
  have hmeas : Measurable (fun b : Bool => !b) := by fun_prop
  have hinj : Function.Injective (fun b : Bool => !b) := by intro x y h; simpa using h
  have hinv : (fun b : Bool => !b) ∘ (fun b : Bool => !b) = id := by funext b; simp
  have hle1 := hinj.map_count_le hmeas
  have hle2 : (Measure.count : Measure Bool) ≤ Measure.map (fun b => !b) Measure.count := by
    calc (Measure.count : Measure Bool)
        = Measure.map ((fun b => !b) ∘ (fun b => !b)) Measure.count := by rw [hinv, Measure.map_id]
      _ = Measure.map (fun b => !b) (Measure.map (fun b => !b) Measure.count) := by
            rw [Measure.map_map hmeas hmeas]
      _ ≤ Measure.map (fun b => !b) Measure.count := Measure.map_mono hle1 hmeas
  exact le_antisymm hle1 hle2
















theorem osp_naive_per_partition_glue_false :
    ¬ (∀ {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] (μ : Measure Ω) (ν : Measure β)
        (h₀ h₁ : Ω → β) (p : Ω → Prop) [DecidablePred p]
        (_h0 : MeasurePreserving h₀ μ ν) (_h1 : MeasurePreserving h₁ μ ν)
        (h : Ω → β) (_hpiece : ∀ x, h x = if p x then h₀ x else h₁ x),
        MeasurePreserving h μ ν) := by
  intro H
  have h0 : MeasurePreserving (id : Bool → Bool) Measure.count Measure.count :=
    ⟨measurable_id, by rw [Measure.map_id]⟩
  have h1 : MeasurePreserving (fun b : Bool => !b) Measure.count Measure.count :=
    ⟨by fun_prop, osp_map_not_count⟩
  
  have key := H Measure.count Measure.count id (fun b => !b) (fun b : Bool => b = true)
    h0 h1 (fun _ => true) (by intro x; cases x <;> simp)
  
  have hbad : (Measure.map (fun _ : Bool => true) Measure.count) {false} = 0 := by
    rw [Measure.map_apply (by fun_prop) (by trivial)]
    have : (fun _ : Bool => true) ⁻¹' ({false} : Set Bool) = ∅ := by ext x; simp
    rw [this]; simp
  have hgood : (Measure.count : Measure Bool) {false} ≠ 0 := by
    rw [Measure.count_apply_finite _ (Set.toFinite _)]; simp
  rw [key.map_eq] at hbad
  exact hgood hbad

end AdaptDisintegration

end OSSS

end StatMech
