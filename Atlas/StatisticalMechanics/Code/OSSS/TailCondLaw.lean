/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Code.OSSS.AdaptCondReduction

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











lemma atc_adaptWt_join_indep_head {n : ℕ} (t s m : ℕ) (hst : t ≤ s)
    (A A' : {i : Fin n // (i : ℕ) < t} → ℝ) (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ)
    (V : Fin n → ℝ) :
    adaptWt (acp_join t A B) V m s = adaptWt (acp_join t A' B) V m s := by
  funext i
  unfold adaptWt
  by_cases h1 : (i : ℕ) < s
  · simp [h1]
  · simp only [h1, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]
      have hit : ¬ (i : ℕ) < t := by omega
      show acp_join t A B i = acp_join t A' B i
      have e1 : acp_join t A B i = if h : (i : ℕ) < t then A ⟨i, h⟩ else B ⟨i, h⟩ := rfl
      have e2 : acp_join t A' B i = if h : (i : ℕ) < t then A' ⟨i, h⟩ else B ⟨i, h⟩ := rfl
      rw [e1, e2, dif_neg hit, dif_neg hit]
    · simp [h2]







noncomputable def atc_innerFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (t : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) (m s : ℕ) : ℝ :=
  ∫ B, (∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n))
    ∂(ubfTail n t)



lemma atc_innerFixed_const_head (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (t s m : ℕ) (hst : t ≤ s)
    (A A' : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atc_innerFixed μ σ g t A m s = atc_innerFixed μ σ g t A' m s := by
  unfold atc_innerFixed
  congr 1; funext B; congr 1; funext V
  rw [atc_adaptWt_join_indep_head t s m hst A A' B V]






lemma atc_avg_innerFixed (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ} {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg)
    (t m s : ℕ) :
    (∫ A, atc_innerFixed μ σ g t A m s ∂(ubfHead n t)) = ∑ x, g x * μ x := by
  
  have hfull := adsD_integral_g_adaptWt_fixed μ hpos hμ1 σ g s m
  have hgmeas : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) :=
    (measurable_g_codeMap μ σ g).comp (measurable_adaptWt_fixed m s)
  have hgbdd : ∀ p : (Fin n → ℝ) × (Fin n → ℝ),
      |g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))| ≤ Cg := fun p => hgC _
  
  set φ : (Fin n → ℝ) → ℝ := fun U =>
    ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt U V m s)) ∂(Vcube n) with hφ
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) ((Vcube n).prod (Vcube n)) :=
    ContinuousFKG.integrable_of_bdd _ hgmeas hgbdd
  have hfubini : (∫ p, g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))
        ∂((Vcube n).prod (Vcube n)))
      = ∫ U, φ U ∂(Vcube n) := by rw [integral_prod _ hint]
  have hφm : Measurable φ := by
    rw [hφ]; exact hgmeas.stronglyMeasurable.integral_prod_right'.measurable
  have hφC : ∀ U, |φ U| ≤ Cg := by
    intro U; rw [hφ]
    calc |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt U V m s)) ∂(Vcube n)|
        ≤ ∫ V, |g (codeMap μ (σ : Fin n → E) (adaptWt U V m s))| ∂(Vcube n) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ V, Cg ∂(Vcube n) := integral_mono
          (ContinuousFKG.integrable_of_bdd _
            ((measurable_g_codeMap μ σ g).comp
              ((measurable_adaptWt_fixed m s).comp (measurable_const.prodMk measurable_id))).abs
            (fun V => by rw [abs_abs]; exact hgC _))
          (integrable_const Cg) (fun V => hgC _)
      _ = Cg := by simp
  
  have hsplit : (∫ U, φ U ∂(cube n))
      = ∫ A, (∫ B, φ ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := by
    have h := ubf_integral_factor n t
      (h₀ := fun _ : {i : Fin n // (i : ℕ) < t} → ℝ => (1 : ℝ))
      measurable_const (Ch := 1) (fun _ => by norm_num) hφm hφC
    simpa using h
  rw [hfull] at hfubini
  
  have key : (∫ A, atc_innerFixed μ σ g t A m s ∂(ubfHead n t))
      = ∫ A, (∫ B, φ ((ubfSplit n t).symm (A, B)) ∂(ubfTail n t)) ∂(ubfHead n t) := rfl
  rw [key, ← hsplit]
  exact hfubini.symm












theorem atc_innerFixed_eq_mean (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ} {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s m : ℕ) (hst : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    atc_innerFixed μ σ g t A m s = Lindeberg.mean μ g := by
  
  
  have hconst : ∀ A', atc_innerFixed μ σ g t A' m s = atc_innerFixed μ σ g t A m s :=
    fun A' => atc_innerFixed_const_head μ σ g t s m hst A' A
  have havg : (∫ A', atc_innerFixed μ σ g t A' m s ∂(ubfHead n t)) = ∑ x, g x * μ x :=
    atc_avg_innerFixed μ hpos hμ1 σ hgC t m s
  show atc_innerFixed μ σ g t A m s = ∑ x, g x * μ x
  rw [← havg]
  rw [show (∫ A', atc_innerFixed μ σ g t A' m s ∂(ubfHead n t))
        = ∫ _A', atc_innerFixed μ σ g t A m s ∂(ubfHead n t) from by
    congr 1; funext A'; exact hconst A']
  rw [integral_const, probReal_univ]; simp









noncomputable def atc_fiberDiagFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (m s : ℕ) (U : Fin n → ℝ) : ℝ :=
  ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s)) ∂(Vcube n)


noncomputable def atc_fiberMargFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (m s : ℕ) (U : Fin n → ℝ) : ℝ :=
  ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt U V m s)) ∂(Vcube n)







theorem atc_tailCondLawFixedDiag (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (t s m : ℕ) (hst : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, atc_fiberDiagFixed μ σ f e m s (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
  have hgC : ∀ ω, |f ω * Lindeberg.coord e ω| ≤ 1 := by
    intro ω; rw [abs_mul, ← one_mul (1 : ℝ)]
    exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num)
  have h := atc_innerFixed_eq_mean μ hpos hμ1 σ (g := fun ω => f ω * Lindeberg.coord e ω)
    hgC t s m hst A
  
  show atc_innerFixed μ σ (fun ω => f ω * Lindeberg.coord e ω) t A m s
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
  exact h



theorem atc_tailCondLawFixedMarg (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ} {Cg : ℝ}
    (hgC : ∀ ω, |g ω| ≤ Cg) (t s m : ℕ) (hst : t ≤ s)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    (∫ B, atc_fiberMargFixed μ σ g m s (acp_join t A B) ∂(ubfTail n t))
      = Lindeberg.mean μ g := by
  show atc_innerFixed μ σ g t A m s = Lindeberg.mean μ g
  exact atc_innerFixed_eq_mean μ hpos hμ1 σ hgC t s m hst A












lemma atc_hasFKG_ubfTail (n t : ℕ) : HasFKG (ubfTail n t) := by
  show HasFKG (Measure.pi (fun _ : {i : Fin n // ¬ (i : ℕ) < t} => unitMeasure))
  set ι := {i : Fin n // ¬ (i : ℕ) < t}
  set k := Fintype.card ι with hk
  set e : ι ≃ Fin k := Fintype.equivFin ι with he
  have hpi : HasFKG (Measure.pi (fun _ : Fin k => unitMeasure)) := hasFKG_pi_unitMeasure k
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e)
      (Measure.pi (fun _ : ι => unitMeasure)) (Measure.pi (fun _ : Fin k => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin k => unitMeasure) e
    convert h using 2
  refine hasFKG_of_orderIso _ _ (MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e) hmp ?_ hpi
  intro p q hpq i
  have ep : ∀ (r : Fin k → ℝ),
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e).symm r) i = r (e i) := by
    intro r; simp [MeasurableEquiv.piCongrLeft]
  show ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e).symm p) i
      ≤ ((MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) e).symm q) i
  rw [ep p, ep q]; exact hpq _


lemma atc_joint_meas_BV (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ)
    (t m s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) =>
      g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A p.1) p.2 m s))) := by
  refine (measurable_g_codeMap μ σ g).comp ?_
  apply measurable_pi_lambda
  intro i; unfold adaptWt
  by_cases h1 : (i : ℕ) < s
  · simp only [h1, if_true]; exact (measurable_pi_apply i).comp measurable_snd
  · simp only [h1, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]
      have hrw : (fun p : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) × (Fin n → ℝ) => acp_join t A p.1 i)
          = (fun p => if h : (i : ℕ) < t then A ⟨i, h⟩ else p.1 ⟨i, h⟩) := rfl
      rw [hrw]
      by_cases h3 : (i : ℕ) < t
      · simp only [dif_pos h3]; exact measurable_const
      · simp only [dif_neg h3]; exact (measurable_pi_apply _).comp measurable_fst
    · simp only [h2, if_false]; exact (measurable_pi_apply i).comp measurable_snd


lemma atc_marg_meas_B (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ)
    (t m s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Measurable (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ =>
      ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)) :=
  (atc_joint_meas_BV μ σ g t m s A).stronglyMeasurable.integral_prod_right'.measurable




lemma atc_marg_mono_B {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ}
    (hg : Monotone g) {Cg : ℝ} (hgC : ∀ ω, |g ω| ≤ Cg) (t m s : ℕ)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Monotone (fun B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ =>
      ∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)) := by
  intro B B' hBB
  apply integral_mono
  · exact ContinuousFKG.integrable_of_bdd _
      ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed m s).comp
        (measurable_const.prodMk measurable_id))) (fun V => hgC _)
  · exact ContinuousFKG.integrable_of_bdd _
      ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed m s).comp
        (measurable_const.prodMk measurable_id))) (fun V => hgC _)
  · intro V
    apply hg; apply codeMap_mono_u hpos hmono
    intro i; unfold adaptWt
    by_cases h1 : (i : ℕ) < s
    · simp [h1]
    · simp only [h1, if_false]
      by_cases h2 : (i : ℕ) < m
      · simp only [h2, if_true]
        have e1 : acp_join t A B i = if h : (i : ℕ) < t then A ⟨i, h⟩ else B ⟨i, h⟩ := rfl
        have e2 : acp_join t A B' i = if h : (i : ℕ) < t then A ⟨i, h⟩ else B' ⟨i, h⟩ := rfl
        rw [e1, e2]
        by_cases h3 : (i : ℕ) < t
        · rw [dif_pos h3, dif_pos h3]
        · rw [dif_neg h3, dif_neg h3]; exact hBB ⟨i, h3⟩
      · simp [h2]


lemma atc_marg_le_one (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) {g : ConfigSpace E → ℝ}
    (hgC : ∀ ω, |g ω| ≤ 1) (t m s : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ)
    (B : {i : Fin n // ¬ (i : ℕ) < t} → ℝ) :
    |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)| ≤ 1 := by
  calc |∫ V, g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s)) ∂(Vcube n)|
      ≤ ∫ V, |g (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s))| ∂(Vcube n) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ V, (1 : ℝ) ∂(Vcube n) := integral_mono
        (ContinuousFKG.integrable_of_bdd _
          ((measurable_g_codeMap μ σ g).comp ((measurable_adaptWt_fixed m s).comp
            (measurable_const.prodMk measurable_id))).abs
          (fun V => by rw [abs_abs]; exact hgC _))
        (integrable_const 1) (fun V => hgC _)
    _ = 1 := by simp



noncomputable def atc_fiberCrossFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (m s₁ s₂ : ℕ) (U : Fin n → ℝ) : ℝ :=
  (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) ∂(Vcube n))
    * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n))









theorem atc_tailCondLawFixedCross {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (e : E)
    (t s₁ s₂ m : ℕ) (hst1 : t ≤ s₁) (hst2 : t ≤ s₂)
    (A : {i : Fin n // (i : ℕ) < t} → ℝ) :
    Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
      ≤ ∫ B, atc_fiberCrossFixed μ σ f e m s₁ s₂ (acp_join t A B) ∂(ubfTail n t) := by
  set φ₁ : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) → ℝ := fun B =>
    ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s₁)) ∂(Vcube n) with hφ₁
  set φ₂ : ({i : Fin n // ¬ (i : ℕ) < t} → ℝ) → ℝ := fun B =>
    ∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt (acp_join t A B) V m s₂)) ∂(Vcube n)
    with hφ₂
  
  have hcross : (∫ B, atc_fiberCrossFixed μ σ f e m s₁ s₂ (acp_join t A B) ∂(ubfTail n t))
      = ∫ B, φ₁ B * φ₂ B ∂(ubfTail n t) := rfl
  rw [hcross]
  
  have hFKG := atc_hasFKG_ubfTail n t φ₁ φ₂
    (atc_marg_meas_B μ σ f t m s₁ A) (atc_marg_meas_B μ σ (Lindeberg.coord e) t m s₂ A)
    ⟨1, fun B => atc_marg_le_one μ σ hfC t m s₁ A B⟩
    ⟨1, fun B => atc_marg_le_one μ σ (fun ω => GrandCoupling.abs_coord_le_one e ω) t m s₂ A B⟩
    (atc_marg_mono_B hpos hmono σ hf hfC t m s₁ A)
    (atc_marg_mono_B hpos hmono σ (Lindeberg.coord_mono e)
      (fun ω => GrandCoupling.abs_coord_le_one e ω) t m s₂ A)
  
  have hm1 : (∫ B, φ₁ B ∂(ubfTail n t)) = Lindeberg.mean μ f :=
    atc_tailCondLawFixedMarg μ hpos hμ1 σ hfC t s₁ m hst1 A
  have hm2 : (∫ B, φ₂ B ∂(ubfTail n t)) = Lindeberg.mean μ (Lindeberg.coord e) :=
    atc_tailCondLawFixedMarg μ hpos hμ1 σ
      (fun ω => GrandCoupling.abs_coord_le_one e ω) t s₂ m hst2 A
  rw [← hm1, ← hm2]
  exact hFKG


















def atc_TailCondLawFixed (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) : Prop :=
  ∀ (t : ℕ) (htn : t < n) (m : ℕ) (A : {i : Fin n // (i : ℕ) < t} → ℝ),
    let e := (σ : Fin n → E) ⟨t, htn⟩
    ((∫ B, atc_fiberDiagFixed μ σ f e m t (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ ((∫ B, atc_fiberDiagFixed μ σ f e m (t+1) (acp_join t A B) ∂(ubfTail n t))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, atc_fiberCrossFixed μ σ f e m t (t+1) (acp_join t A B) ∂(ubfTail n t))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
        ≤ ∫ B, atc_fiberCrossFixed μ σ f e m (t+1) t (acp_join t A B) ∂(ubfTail n t))










theorem atc_tailCondLawFixed {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) :
    atc_TailCondLawFixed μ σ f := by
  intro t htn m A
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact atc_tailCondLawFixedDiag μ hpos hμ1 σ hfC e t t m (le_refl t) A
  · exact atc_tailCondLawFixedDiag μ hpos hμ1 σ hfC e t (t+1) m (Nat.le_succ t) A
  · exact atc_tailCondLawFixedCross hpos hμ1 hmono σ hf hfC e t t (t+1) m (le_refl t)
      (Nat.le_succ t) A
  · exact atc_tailCondLawFixedCross hpos hμ1 hmono σ hf hfC e t (t+1) t m (Nat.le_succ t)
      (le_refl t) A

end AdaptDisintegration

end OSSS

end StatMech
