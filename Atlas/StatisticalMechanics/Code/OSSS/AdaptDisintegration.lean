/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.OSSS.AdaptMConditional

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












def sw2 (n s m : ℕ) : Fin n ⊕ Fin n → Fin n ⊕ Fin n
  | Sum.inl i => if (i : ℕ) < s ∨ (i : ℕ) ≥ m then Sum.inr i else Sum.inl i
  | Sum.inr i => if (i : ℕ) < s ∨ (i : ℕ) ≥ m then Sum.inl i else Sum.inr i

lemma sw2_invol (n s m : ℕ) : Function.Involutive (sw2 n s m) := by
  intro x
  cases x with
  | inl i => by_cases h : (i : ℕ) < s ∨ (i : ℕ) ≥ m <;> simp [sw2, h]
  | inr i => by_cases h : (i : ℕ) < s ∨ (i : ℕ) ≥ m <;> simp [sw2, h]


noncomputable def sw2Equiv (n s m : ℕ) : Equiv.Perm (Fin n ⊕ Fin n) := (sw2_invol n s m).toPerm

lemma sw2Equiv_symm_apply (n s m : ℕ) (x : Fin n ⊕ Fin n) :
    (sw2Equiv n s m).symm x = sw2 n s m x := rfl



noncomputable def selMap2 (n s m : ℕ) : ((Fin n → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ) :=
  fun p => projInl n
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (sw2Equiv n s m)) (combine n p))


lemma adsD_selMap2_eq_adaptWt (n s m : ℕ) (U V : Fin n → ℝ) :
    selMap2 n s m (U, V) = adaptWt U V m s := by
  funext i
  unfold selMap2 projInl adaptWt
  rw [MeasurableEquiv.coe_piCongrLeft]
  simp only [Equiv.piCongrLeft_apply, eq_rec_constant]
  rw [sw2Equiv_symm_apply, combine_apply]
  simp only [sw2]
  by_cases h : (i : ℕ) < s
  · rw [if_pos (Or.inl h)]; simp [h]
  · by_cases h2 : (i : ℕ) < m
    · have hcond : ¬ ((i:ℕ) < s ∨ (i:ℕ) ≥ m) := by
        rintro (hc | hc) <;> omega
      rw [if_neg hcond]; simp [h, h2]
    · have hcond : (i:ℕ) < s ∨ (i:ℕ) ≥ m := Or.inr (by omega)
      rw [if_pos hcond]; simp [h, h2]





lemma adsD_selMap2_measurePreserving (n s m : ℕ) :
    MeasurePreserving (selMap2 n s m) ((Vcube n).prod (Vcube n)) (Vcube n) := by
  show MeasurePreserving (selMap2 n s m)
    ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
    (Measure.pi (fun _ : Fin n => unitMeasure))
  have hcombine : MeasurePreserving (combine n)
      ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) :=
    (measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)).symm _
  have hperm : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ⊕ Fin n => ℝ) (sw2Equiv n s m))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure)) := by
    have h := measurePreserving_piCongrLeft (fun _ : Fin n ⊕ Fin n => unitMeasure) (sw2Equiv n s m)
    convert h using 2
  have hproj : MeasurePreserving (projInl n)
      (Measure.pi (fun _ : Fin n ⊕ Fin n => unitMeasure))
      (Measure.pi (fun _ : Fin n => unitMeasure)) := by
    have hsum := measurePreserving_sumPiEquivProdPi (X := fun _ : Fin n ⊕ Fin n => ℝ)
      (fun _ : Fin n ⊕ Fin n => unitMeasure)
    have hfst : MeasurePreserving Prod.fst
        ((Measure.pi (fun _ : Fin n => unitMeasure)).prod (Measure.pi (fun _ : Fin n => unitMeasure)))
        (Measure.pi (fun _ : Fin n => unitMeasure)) := measurePreserving_fst
    have := hfst.comp hsum
    convert this using 1
  have := (hproj.comp hperm).comp hcombine
  convert this using 1











theorem adsD_integral_g_adaptWt_fixed (μ : ConfigSpace E → ℝ) (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (g : ConfigSpace E → ℝ) (s m : ℕ) :
    ∫ p, g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s)) ∂((Vcube n).prod (Vcube n))
      = ∑ x, g x * μ x := by
  have hmp := adsD_selMap2_measurePreserving n s m
  have hcomp : ∫ p, (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap2 n s m p)
        ∂((Vcube n).prod (Vcube n))
      = ∫ w, g (codeMap μ (σ : Fin n → E) w) ∂(Vcube n) := by
    rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable
      (measurable_g_codeMap μ σ g).aestronglyMeasurable, hmp.map_eq]
  have hrw : (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        (fun w => g (codeMap μ (σ : Fin n → E) w)) (selMap2 n s m p))
      = (fun p => g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) := by
    funext p; rw [show p = (p.1, p.2) from rfl, adsD_selMap2_eq_adaptWt]
  rw [hrw] at hcomp
  rw [hcomp, integral_g_codeMap μ hpos hμ1 σ g]











lemma adsD_measurable_f_adaptWt_fiber (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (m s : ℕ) :
    Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s))) := by
  have hrw : (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s)))
      = (fun V => f (codeMap μ (σ : Fin n → E) (Wt (mixUV U V m) V s))) := by
    funext V; rw [adaptWt_eq_Wt_mix]
  rw [hrw]
  refine (measurable_g_codeMap μ σ f).comp ?_
  apply measurable_pi_lambda
  intro i; unfold Wt mixUV
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact measurable_pi_apply i
  · simp only [h, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]; exact measurable_const
    · simp only [h2, if_false]; exact measurable_pi_apply i



lemma adsD_measurable_f_adaptWt_prod (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (g : ConfigSpace E → ℝ) (m s : ℕ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        g (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s))) :=
  (measurable_g_codeMap μ σ g).comp (measurable_adaptWt_fixed m s)



lemma adsD_adaptWt_mono_V {n : ℕ} (U : Fin n → ℝ) (m s : ℕ) :
    Monotone (fun V : Fin n → ℝ => adaptWt U V m s) := by
  intro V V' hle i
  unfold adaptWt
  by_cases h : (i : ℕ) < s
  · simp only [h, if_true]; exact hle i
  · simp only [h, if_false]
    by_cases h2 : (i : ℕ) < m
    · simp only [h2, if_true]; exact le_refl _
    · simp only [h2, if_false]; exact hle i



lemma adsD_f_adaptWt_mono_V {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (U : Fin n → ℝ) (m s : ℕ) :
    Monotone (fun V : Fin n → ℝ => f (codeMap μ σ (adaptWt U V m s))) :=
  fun _ _ hle => hf ((codeMap_mono_u hpos hmono σ) ((adsD_adaptWt_mono_V U m s) hle))


lemma adsD_coord_adaptWt_mono_V {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n → E) (e : E) (U : Fin n → ℝ) (m s : ℕ) :
    Monotone (fun V : Fin n → ℝ => Lindeberg.coord e (codeMap μ σ (adaptWt U V m s))) :=
  fun _ _ hle =>
    Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono σ) ((adsD_adaptWt_mono_V U m s) hle))



lemma adsD_integrable_prod_obs_fiber (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ)
    (m s₁ s₂ : ℕ) :
    Integrable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂))) (Vcube n) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  refine ContinuousFKG.integrable_of_bdd _
    ((adsD_measurable_f_adaptWt_fiber μ σ f U m s₁).mul
      (adsD_measurable_f_adaptWt_fiber μ σ (Lindeberg.coord e) U m s₂))
    (C := Cf * 1) (fun V => ?_)
  rw [abs_mul]
  exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) hCf0

















theorem adsD_abs_adapt_step_eq_four_terms {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (t m : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) (htn : t - 1 < n)
    (U V : Fin n → ℝ) :
    |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))|
      = f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
        + f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
          * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩) (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) := by
  set k := t - 1 with hk
  set e := (σ : Fin n → E) ⟨k, htn⟩ with he
  set Yt := codeMap μ (σ : Fin n → E) (adaptWt U V m t) with hYt
  set Ys := codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)) with hYs
  
  have hoff : ∀ i : Fin n, (i:ℕ) ≠ k → adaptWt U V m t i = adaptWt U V m (t-1) i :=
    adaptWt_agree_off U V m t ht
  
  have hdet : Lindeberg.coord e Yt = Lindeberg.coord e Ys → Yt = Ys := by
    intro hcoord
    have hbit : Yt e = Ys e := by
      unfold Lindeberg.coord at hcoord
      by_cases h1 : Yt e <;> by_cases h2 : Ys e <;> simp_all
    exact codeMap_det μ (σ : Fin n → E) σ.injective (adaptWt U V m t) (adaptWt U V m (t-1)) k htn
      (fun i hi => hoff i hi) hbit
  
  obtain ⟨hVt, hUt⟩ := adaptWt_at_pos U V m t ht htm htn
  
  have hcmp : (f Ys ≤ f Yt ∧ Lindeberg.coord e Ys ≤ Lindeberg.coord e Yt)
      ∨ (f Yt ≤ f Ys ∧ Lindeberg.coord e Yt ≤ Lindeberg.coord e Ys) := by
    rcases le_total (U ⟨k, htn⟩) (V ⟨k, htn⟩) with hUV | hVU
    · left
      have hle : adaptWt U V m (t-1) ≤ adaptWt U V m t := by
        intro i
        by_cases hi : (i:ℕ) = k
        · have hieq : i = ⟨k, htn⟩ := by ext; rw [hi]
          rw [hieq, hVt, hUt]; exact hUV
        · rw [hoff i hi]
      have hY : Ys ≤ Yt := codeMap_mono_u hpos hmono (σ : Fin n → E) hle
      exact ⟨hf hY, Lindeberg.coord_mono e hY⟩
    · right
      have hle : adaptWt U V m t ≤ adaptWt U V m (t-1) := by
        intro i
        by_cases hi : (i:ℕ) = k
        · have hieq : i = ⟨k, htn⟩ := by ext; rw [hi]
          rw [hieq, hVt, hUt]; exact hVU
        · rw [hoff i hi]
      have hY : Yt ≤ Ys := codeMap_mono_u hpos hmono (σ : Fin n → E) hle
      exact ⟨hf hY, Lindeberg.coord_mono e hY⟩
  exact tt_algebra (f Yt) (f Ys) (Lindeberg.coord e Yt) (Lindeberg.coord e Ys)
    (coord_eq01 e Yt) (coord_eq01 e Ys) hcmp (fun h => by rw [hdet h])






theorem adsD_abs_adapt_step_integral_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t m : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) (htn : t - 1 < n) (U : Fin n → ℝ) :
    (∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
            - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| ∂(Vcube n))
      = (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n))
        + (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  set D1 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) with hD1
  set D2 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) with hD2
  set C1 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) with hC1
  set C2 := fun V => f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) with hC2
  have hI1 : Integrable D1 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m (t-1) (t-1)
  have hI2 : Integrable D2 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m t t
  have hIc1 : Integrable C1 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m (t-1) t
  have hIc2 : Integrable C2 (Vcube n) := adsD_integrable_prod_obs_fiber μ σ hfC e U m t (t-1)
  have hcongr : (∫ V, |f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
            - f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))| ∂(Vcube n))
      = ∫ V, (D1 V + D2 V - C1 V - C2 V) ∂(Vcube n) := by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro V
    exact adsD_abs_adapt_step_eq_four_terms hpos hmono σ hf t m ht htm htn U V
  rw [hcongr]
  have esplit : (fun V => D1 V + D2 V - C1 V - C2 V) = (D1 + D2 - C1) - C2 := by
    funext V; simp only [Pi.add_apply, Pi.sub_apply]
  rw [show (∫ V, (D1 V + D2 V - C1 V - C2 V) ∂(Vcube n))
        = ∫ V, ((D1 + D2 - C1) - C2) V ∂(Vcube n) from by rw [esplit]]
  rw [integral_sub' ((hI1.add hI2).sub hIc1) hIc2]
  rw [show (∫ V, (D1 + D2 - C1) V ∂(Vcube n)) = ∫ V, ((D1 + D2) - C1) V ∂(Vcube n) from rfl]
  rw [integral_sub' (hI1.add hI2) hIc1, integral_add' hI1 hI2]









theorem adsD_adapt_fkg_cross_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (m s₁ s₂ : ℕ)
    (U : Fin n → ℝ) :
    (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V m s₂)) ∂(Vcube n) := by
  refine fkg_second_block_fiber
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s₁)))
    (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 m s₂)))
    (adsD_measurable_f_adaptWt_prod μ σ f m s₁)
    (adsD_measurable_f_adaptWt_prod μ σ (Lindeberg.coord e) m s₂)
    (Cf := Cf) (Cg := 1) (fun z => hfC _) (fun z => GrandCoupling.abs_coord_le_one e _)
    ?_ ?_ U
  · intro Ufix V V' hVV
    exact hf ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((adsD_adaptWt_mono_V Ufix m s₁) hVV))
  · intro Ufix V V' hVV
    exact Lindeberg.coord_mono e
      ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((adsD_adaptWt_mono_V Ufix m s₂) hVV))












theorem adsD_adapt_step_fiber_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t m : ℕ) (ht : 1 ≤ t) (htm : t ≤ m) (htn : t - 1 < n) (U : Fin n → ℝ) :
    (∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
            - f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))| ∂(Vcube n))
      ≤ (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n))
        + (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n))
            * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V m t)) ∂(Vcube n))
            * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (adaptWt U V m (t-1))) ∂(Vcube n)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  rw [adsD_abs_adapt_step_integral_fiber hpos hmono σ hf hfC t m ht htm htn U]
  have key1 : (∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) ∂(Vcube n))
      * (∫ V, Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1)))
            * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) ∂(Vcube n) :=
    adsD_adapt_fkg_cross_fiber hpos hmono σ hf hfC e m (t-1) t U
  have key2 : (∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m t)) ∂(Vcube n))
      * (∫ V, Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ:Fin n→E) (adaptWt U V m t))
            * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (adaptWt U V m (t-1))) ∂(Vcube n) :=
    adsD_adapt_fkg_cross_fiber hpos hmono σ hf hfC e m t (t-1) U
  linarith [key1, key2]




























noncomputable def fiberStep (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (t : ℕ) (U : Fin n → ℝ) : ℝ :=
  ∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) (t+1)))
        - f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) t))| ∂(Vcube n)


noncomputable def fiberDiag (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (s : ℕ) (U : Fin n → ℝ) : ℝ :=
  ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s)) ∂(Vcube n)



noncomputable def fiberCross (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (e : E) (s₁ s₂ : ℕ) (U : Fin n → ℝ) : ℝ :=
  (∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n))
    * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n))








def AdaptCondBBB (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) :
    Prop :=
  ∀ (t : ℕ) (htn : t < n),
    let e := (σ : Fin n → E) ⟨t, htn⟩
    ((∫ U, fiberDiag μ σ f e t U * truncInd μ σ f U (t+1) ∂(Vcube n))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
            * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n))
    ∧ ((∫ U, fiberDiag μ σ f e (t+1) U * truncInd μ σ f U (t+1) ∂(Vcube n))
        = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω)
            * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
          * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n)
        ≤ ∫ U, fiberCross μ σ f e t (t+1) U * truncInd μ σ f U (t+1) ∂(Vcube n))
    ∧ (Lindeberg.mean μ f * Lindeberg.mean μ (Lindeberg.coord e)
          * ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n)
        ≤ ∫ U, fiberCross μ σ f e (t+1) t U * truncInd μ σ f U (t+1) ∂(Vcube n))


lemma truncInd_nonneg (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (t : ℕ) : 0 ≤ truncInd μ σ f U t := by
  unfold truncInd; split <;> norm_num



lemma adsD_fubini_lhs (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) :
    (∫ p, |f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) (t+1)))
          - f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) t))|
          * truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)))
      = ∫ U, fiberStep μ σ f t U * truncInd μ σ f U (t+1) ∂(Vcube n) := by
  have hint := integrable_abs_adapt_step_trunc μ σ hfC t
  rw [integral_prod _ hint]
  apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
  simp only
  rw [integral_mul_const]; rfl



lemma adsD_integrable_fiberStep (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (t : ℕ) :
    Integrable (fun U => fiberStep μ σ f t U * truncInd μ σ f U (t+1)) (Vcube n) := by
  have hint := (integrable_abs_adapt_step_trunc μ σ hfC t).integral_prod_left
  simp only at hint
  refine hint.congr (Filter.Eventually.of_forall (fun U => ?_))
  show (∫ V, _ * _ ∂(Vcube n)) = fiberStep μ σ f t U * truncInd μ σ f U (t+1)
  rw [integral_mul_const]; rfl



lemma adsD_integrable_fiberDiag (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (s : ℕ) (t : ℕ) :
    Integrable (fun U => fiberDiag μ σ f e s U * truncInd μ σ f U (t+1)) (Vcube n) := by
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      (f (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt p.1 p.2 (stopVal μ σ f p.1) s)))
        * truncInd μ σ f p.1 (t+1)) ((Vcube n).prod (Vcube n)) := by
    refine ContinuousFKG.integrable_of_bdd _
      (((measurable_g_adaptWt μ σ f f s).mul (measurable_g_adaptWt μ σ f (Lindeberg.coord e) s)).mul
        ((measurable_truncInd μ σ f (t+1)).comp measurable_fst)) (C := (1*1)*1) (fun p => ?_)
    rw [abs_mul, abs_mul]
    refine mul_le_mul (mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) (by norm_num))
      (truncInd_le_one μ σ f p.1 (t+1)) (abs_nonneg _) (by positivity)
  have hm := hint.integral_prod_left
  simp only at hm
  refine hm.congr (Filter.Eventually.of_forall (fun U => ?_))
  show (∫ V, _ * _ ∂(Vcube n)) = fiberDiag μ σ f e s U * truncInd μ σ f U (t+1)
  rw [integral_mul_const]; rfl



lemma adsD_integrable_fiberCross (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hfC : ∀ ω, |f ω| ≤ 1) (e : E) (s₁ s₂ : ℕ) (t : ℕ) :
    Integrable (fun U => fiberCross μ σ f e s₁ s₂ U * truncInd μ σ f U (t+1)) (Vcube n) := by
  
  have hmf : Measurable (fun U : Fin n → ℝ =>
      ∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n)) :=
    ((measurable_g_adaptWt μ σ f f s₁).stronglyMeasurable.integral_prod_right').measurable
  have hmg : Measurable (fun U : Fin n → ℝ =>
      ∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n)) :=
    ((measurable_g_adaptWt μ σ f (Lindeberg.coord e) s₂).stronglyMeasurable.integral_prod_right').measurable
  have hbf : ∀ U, |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n)| ≤ 1 := by
    intro U
    calc |∫ V, f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁)) ∂(Vcube n)|
        ≤ ∫ V, |f (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₁))| ∂(Vcube n) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ V, (1:ℝ) ∂(Vcube n) :=
          integral_mono (ContinuousFKG.integrable_of_bdd _
            (((measurable_g_adaptWt μ σ f f s₁).comp (measurable_const.prodMk measurable_id)).abs)
            (fun V => by rw [abs_abs]; exact hfC _))
            (integrable_const 1) (fun V => hfC _)
      _ = 1 := by simp
  have hbg : ∀ U, |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n)| ≤ 1 := by
    intro U
    calc |∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂)) ∂(Vcube n)|
        ≤ ∫ V, |Lindeberg.coord e (codeMap μ (σ : Fin n → E) (adaptWt U V (stopVal μ σ f U) s₂))| ∂(Vcube n) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ V, (1:ℝ) ∂(Vcube n) :=
          integral_mono (ContinuousFKG.integrable_of_bdd _
            (((measurable_g_adaptWt μ σ f (Lindeberg.coord e) s₂).comp (measurable_const.prodMk measurable_id)).abs)
              (fun V => by rw [abs_abs]; exact GrandCoupling.abs_coord_le_one e _))
            (integrable_const 1) (fun V => GrandCoupling.abs_coord_le_one e _)
      _ = 1 := by simp
  refine ContinuousFKG.integrable_of_bdd _
    ((hmf.mul hmg).mul (measurable_truncInd μ σ f (t+1))) (C := (1*1)*1) (fun U => ?_)
  unfold fiberCross
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul (hbf U) (hbg U) (abs_nonneg _) (by norm_num))
    (truncInd_le_one μ σ f U (t+1)) (abs_nonneg _) (by positivity)









theorem adsD_adaptStepCovBound_of_condBBB {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hfC : ∀ ω, |f ω| ≤ 1) (hBBB : AdaptCondBBB μ σ f) :
    AdaptMConditional.AdaptStepCovBound μ σ f := by
  intro t htn
  set e := (σ : Fin n → E) ⟨t, htn⟩ with he
  
  rw [adsD_fubini_lhs μ σ hfC t]
  
  have hpt : ∀ U, fiberStep μ σ f t U * truncInd μ σ f U (t+1)
      ≤ (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
          - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
        * truncInd μ σ f U (t+1) := by
    intro U
    unfold truncInd
    by_cases hev : t + 1 ≤ stopVal μ σ f U
    · rw [if_pos hev, mul_one, mul_one]
      
      
      have htn' : (t+1) - 1 < n := by simpa using htn
      have hbound := adsD_adapt_step_fiber_le hpos hmono σ hf hfC (t+1) (stopVal μ σ f U)
        (Nat.succ_le_succ (Nat.zero_le _)) hev htn' U
      
      
      unfold fiberStep fiberDiag fiberCross
      convert hbound using 2
    · rw [if_neg hev, mul_zero, mul_zero]
  
  refine (integral_mono (adsD_integrable_fiberStep μ σ hfC t) ?_ hpt).trans ?_
  · 
    have h1 := adsD_integrable_fiberDiag μ σ hfC e t t
    have h2 := adsD_integrable_fiberDiag μ σ hfC e (t+1) t
    have h3 := adsD_integrable_fiberCross μ σ hfC e t (t+1) t
    have h4 := adsD_integrable_fiberCross μ σ hfC e (t+1) t t
    have hcomb : (fun U => (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
          - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
        * truncInd μ σ f U (t+1))
        = (fun U => fiberDiag μ σ f e t U * truncInd μ σ f U (t+1)
            + fiberDiag μ σ f e (t+1) U * truncInd μ σ f U (t+1)
            - fiberCross μ σ f e t (t+1) U * truncInd μ σ f U (t+1)
            - fiberCross μ σ f e (t+1) t U * truncInd μ σ f U (t+1)) := by
      funext U; ring
    rw [hcomb]
    exact ((h1.add h2).sub h3).sub h4
  · 
    obtain ⟨hD1, hD2, hC1, hC2⟩ := hBBB t htn
    set A1 := fun U => fiberDiag μ σ f e t U * truncInd μ σ f U (t+1) with hA1
    set A2 := fun U => fiberDiag μ σ f e (t+1) U * truncInd μ σ f U (t+1) with hA2
    set B1 := fun U => fiberCross μ σ f e t (t+1) U * truncInd μ σ f U (t+1) with hB1
    set B2 := fun U => fiberCross μ σ f e (t+1) t U * truncInd μ σ f U (t+1) with hB2
    have h1 : Integrable A1 (Vcube n) := adsD_integrable_fiberDiag μ σ hfC e t t
    have h2 : Integrable A2 (Vcube n) := adsD_integrable_fiberDiag μ σ hfC e (t+1) t
    have h3 : Integrable B1 (Vcube n) := adsD_integrable_fiberCross μ σ hfC e t (t+1) t
    have h4 : Integrable B2 (Vcube n) := adsD_integrable_fiberCross μ σ hfC e (t+1) t t
    have hsplit : (∫ U, (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
          - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
        * truncInd μ σ f U (t+1) ∂(Vcube n))
      = (∫ U, A1 U ∂(Vcube n)) + (∫ U, A2 U ∂(Vcube n))
        - (∫ U, B1 U ∂(Vcube n)) - (∫ U, B2 U ∂(Vcube n)) := by
      rw [show (fun U => (fiberDiag μ σ f e t U + fiberDiag μ σ f e (t+1) U
            - fiberCross μ σ f e t (t+1) U - fiberCross μ σ f e (t+1) t U)
          * truncInd μ σ f U (t+1)) = (A1 + A2 - B1) - B2 from by
        funext U; simp only [Pi.add_apply, Pi.sub_apply, hA1, hA2, hB1, hB2]; ring]
      rw [integral_sub' ((h1.add h2).sub h3) h4]
      rw [show (∫ U, (A1 + A2 - B1) U ∂(Vcube n)) = ∫ U, ((A1 + A2) - B1) U ∂(Vcube n) from rfl]
      rw [integral_sub' (h1.add h2) h3, integral_add' h1 h2]
    rw [hsplit]
    
    set δ := ∫ U, truncInd μ σ f U (t+1) ∂(Vcube n) with hδ
    set Mfe := Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) with hMfe
    set Mf := Lindeberg.mean μ f with hMf
    set Mc := Lindeberg.mean μ (Lindeberg.coord e) with hMc
    
    have eA1 : (∫ U, A1 U ∂(Vcube n)) = Mfe * δ := hD1
    have eA2 : (∫ U, A2 U ∂(Vcube n)) = Mfe * δ := hD2
    have eB1 : Mf * Mc * δ ≤ ∫ U, B1 U ∂(Vcube n) := hC1
    have eB2 : Mf * Mc * δ ≤ ∫ U, B2 U ∂(Vcube n) := hC2
    have hcov : Lindeberg.cov μ f (Lindeberg.coord e) = Mfe - Mf * Mc := rfl
    have hδeq : δ = ∫ p, truncInd μ σ f p.1 (t + 1) ∂((Vcube n).prod (Vcube n)) := by
      rw [hδ, integral_prod _ (integrable_truncInd μ σ f (t+1))]
      apply integral_congr_ae; apply Filter.Eventually.of_forall; intro U
      simp only; rw [integral_const]; simp
    rw [hcov, ← hδeq]
    
    rw [eA1, eA2]
    nlinarith [eB1, eB2]























theorem adsD_tree_osss_sharp {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hBBB : AdaptCondBBB μ σ f) :
    Lindeberg.var μ f
      ≤ ∑ e, AdaptMConditional.revealAdapt μ σ f e
          * Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hf0' : ∀ ω, (0:ℝ) ≤ f ω := fun ω => hf0 ω
  have hfC : ∀ ω, |f ω| ≤ 1 := fun ω => by
    rw [abs_le]; exact ⟨by linarith [hf0' ω], hf1 ω⟩
  exact AdaptMConditional.tree_osss_sharp_unconditional hpos hμ1 σ hf0 hf1
    (adsD_adaptStepCovBound_of_condBBB hpos hmono σ hf hfC hBBB)

section FK

open StatMech.OSSS.MonotonicFK











theorem adsD_fk_q2_sharp {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {n : ℕ} (σ : Fin n ≃ Sym2 V) {f : ConfigSpace (Sym2 V) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hBBB : AdaptCondBBB (fkMass G p 2) σ f) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, AdaptMConditional.revealAdapt (fkMass G p 2) σ f e
          * Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  adsD_tree_osss_sharp
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) σ hf hf0 hf1 hBBB

end FK

end AdaptDisintegration

end OSSS

end StatMech
