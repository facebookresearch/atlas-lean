/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Code.OSSS.GrandCouplingAssembly
import Code.OSSS.StepCov
import Code.Probability.ContinuousFKGAdapter

open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace AdaptiveTau

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly
open StatMech.Probability OSSS.LindebergTree OSSS.StepCov OSSS.DecisionTree

variable {E : Type*} [Fintype E] [DecidableEq E]








lemma Vcube_eq_cube (n : ℕ) : Vcube n = cube n := rfl



lemma measurable_f_codeMap_Wt_fiber (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    (f : ConfigSpace E → ℝ) (U : Fin n → ℝ) (s : ℕ) :
    Measurable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s))) :=
  measurable_f_codeMap_Wt μ σ f U s



lemma integrable_prod_obs_fiber (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n ≃ E)
    {f : ConfigSpace E → ℝ} {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (U : Fin n → ℝ)
    (s₁ s₂ : ℕ) :
    Integrable (fun V : Fin n → ℝ => f (codeMap μ (σ : Fin n → E) (Wt U V s₁))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂))) (Vcube n) := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hfC (fun _ => false))
  refine ContinuousFKG.integrable_of_bdd _
    ((measurable_f_codeMap_Wt μ σ f U s₁).mul (measurable_coord_codeMap_Wt μ σ e U s₂))
    (C := Cf * 1) (fun V => ?_)
  rw [abs_mul]
  exact mul_le_mul (hfC _) (GrandCoupling.abs_coord_le_one e _) (abs_nonneg _) hCf0


















theorem grandCoupling_fkg_cross_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (s₁ s₂ : ℕ)
    (U : Fin n → ℝ) :
    (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n) := by
  refine fkg_second_block_fiber
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)))
    (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂)))
    (measurable_g_codeMap_Wt_prod μ σ f s₁)
    (measurable_g_codeMap_Wt_prod μ σ (Lindeberg.coord e) s₂)
    (Cf := Cf) (Cg := 1) (fun z => hfC _) (fun z => GrandCoupling.abs_coord_le_one e _)
    ?_ ?_ U
  · intro Ufix V V' hVV
    exact hf ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((Wt_mono_V Ufix s₁) hVV))
  · intro Ufix V V' hVV
    exact Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((Wt_mono_V Ufix s₂) hVV))






theorem osss_grand_coupling_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (t : ℕ)
    (U : Fin n → ℝ) :
    ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t - 1)))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
    ∧ ((∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V (t - 1))) ∂(Vcube n)) :=
  ⟨grandCoupling_fkg_cross_fiber hpos hmono σ hf hfC e (t - 1) t U,
   grandCoupling_fkg_cross_fiber hpos hmono σ hf hfC e t (t - 1) U⟩















theorem abs_step_integral_fiber {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t : ℕ) (ht : 1 ≤ t) (htn : t - 1 < n) (U : Fin n → ℝ) :
    (∫ V, |f (codeMap μ (σ : Fin n → E) (Wt U V t))
            - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))| ∂(Vcube n))
      = (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n))
        + (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  set D1 := fun V => f (codeMap μ (σ:Fin n→E) (Wt U V (t-1)))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V (t-1))) with hD1
  set D2 := fun V => f (codeMap μ (σ:Fin n→E) (Wt U V t))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V t)) with hD2
  set C1 := fun V => f (codeMap μ (σ:Fin n→E) (Wt U V (t-1)))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V t)) with hC1
  set C2 := fun V => f (codeMap μ (σ:Fin n→E) (Wt U V t))
      * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V (t-1))) with hC2
  have hI1 : Integrable D1 (Vcube n) := integrable_prod_obs_fiber μ σ hfC e U (t-1) (t-1)
  have hI2 : Integrable D2 (Vcube n) := integrable_prod_obs_fiber μ σ hfC e U t t
  have hIc1 : Integrable C1 (Vcube n) := integrable_prod_obs_fiber μ σ hfC e U (t-1) t
  have hIc2 : Integrable C2 (Vcube n) := integrable_prod_obs_fiber μ σ hfC e U t (t-1)
  have hcongr : (∫ V, |f (codeMap μ (σ:Fin n→E) (Wt U V t))
            - f (codeMap μ (σ:Fin n→E) (Wt U V (t-1)))| ∂(Vcube n))
      = ∫ V, (D1 V + D2 V - C1 V - C2 V) ∂(Vcube n) := by
    apply integral_congr_ae; apply Filter.Eventually.of_forall; intro V
    exact abs_step_eq_four_terms hpos hmono σ hf t ht htn U V
  rw [hcongr]
  have esplit : (fun V => D1 V + D2 V - C1 V - C2 V) = (D1 + D2 - C1) - C2 := by
    funext V; simp only [Pi.add_apply, Pi.sub_apply]
  rw [show (∫ V, (D1 V + D2 V - C1 V - C2 V) ∂(Vcube n))
        = ∫ V, ((D1 + D2 - C1) - C2) V ∂(Vcube n) from by rw [esplit]]
  rw [integral_sub' ((hI1.add hI2).sub hIc1) hIc2]
  rw [show (∫ V, (D1 + D2 - C1) V ∂(Vcube n)) = ∫ V, ((D1 + D2) - C1) V ∂(Vcube n) from rfl]
  rw [integral_sub' (hI1.add hI2) hIc1, integral_add' hI1 hI2]






















theorem step_fiber_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf)
    (t : ℕ) (ht : 1 ≤ t) (htn : t - 1 < n) (U : Fin n → ℝ) :
    (∫ V, |f (codeMap μ (σ : Fin n → E) (Wt U V t))
            - f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))| ∂(Vcube n))
      ≤ (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1)))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n))
        + (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t))
              * Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n))
            * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
        - (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V t)) ∂(Vcube n))
            * (∫ V, Lindeberg.coord ((σ : Fin n → E) ⟨t-1, htn⟩)
                  (codeMap μ (σ : Fin n → E) (Wt U V (t-1))) ∂(Vcube n)) := by
  set e := (σ : Fin n → E) ⟨t-1, htn⟩ with he
  rw [abs_step_integral_fiber hpos hmono σ hf hfC t ht htn U]
  
  obtain ⟨hcross1, hcross2⟩ := osss_grand_coupling_fiber hpos hmono σ hf hfC e t U
  
  have hstep : (1:ℕ) ≤ t := ht
  
  have key1 : (∫ V, f (codeMap μ (σ:Fin n→E) (Wt U V (t-1))) ∂(Vcube n))
      * (∫ V, Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V t)) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ:Fin n→E) (Wt U V (t-1)))
            * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V t)) ∂(Vcube n) := hcross1
  have key2 : (∫ V, f (codeMap μ (σ:Fin n→E) (Wt U V t)) ∂(Vcube n))
      * (∫ V, Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V (t-1))) ∂(Vcube n))
      ≤ ∫ V, f (codeMap μ (σ:Fin n→E) (Wt U V t))
            * Lindeberg.coord e (codeMap μ (σ:Fin n→E) (Wt U V (t-1))) ∂(Vcube n) := hcross2
  linarith [key1, key2]





















theorem integral_U_diagonal_eq_bbb {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} {Cf : ℝ}
    (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (s : ℕ) :
    (∫ U, (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s)) ∂(Vcube n)) ∂(Vcube n))
      = Lindeberg.mean μ (fun ω => f ω * Lindeberg.coord e ω) := by
  have hint : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s))
        * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s)))
      ((Vcube n).prod (Vcube n)) := integrable_prod_obs μ σ hfC e s s
  rw [← integral_prod _ hint]
  exact integral_g_codeMap_Wt μ hpos hμ1 σ (fun ω => f ω * Lindeberg.coord e ω) s







theorem integral_U_cross_le {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hmono : IsMonotonicMeasure μ) {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) {Cf : ℝ} (hfC : ∀ ω, |f ω| ≤ Cf) (e : E) (s₁ s₂ : ℕ) :
    (∫ U, (∫ V, f (codeMap μ (σ : Fin n → E) (Wt U V s₁)) ∂(Vcube n))
          * (∫ V, Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt U V s₂)) ∂(Vcube n))
          ∂(Vcube n))
      ≤ ∫ p, f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁))
            * Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂))
          ∂((Vcube n).prod (Vcube n)) := by
  refine fkg_second_block
    (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => f (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₁)))
    (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
        Lindeberg.coord e (codeMap μ (σ : Fin n → E) (Wt p.1 p.2 s₂)))
    (measurable_g_codeMap_Wt_prod μ σ f s₁)
    (measurable_g_codeMap_Wt_prod μ σ (Lindeberg.coord e) s₂)
    (Cf := Cf) (Cg := 1) (fun z => hfC _) (fun z => GrandCoupling.abs_coord_le_one e _)
    ?_ ?_
  · intro Ufix V V' hVV
    exact hf ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((Wt_mono_V Ufix s₁) hVV))
  · intro Ufix V V' hVV
    exact Lindeberg.coord_mono e ((codeMap_mono_u hpos hmono (σ : Fin n → E)) ((Wt_mono_V Ufix s₂) hVV))




































theorem tree_osss {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (T : DecisionTree E) (hStep : StepCovBoundTwo μ T (T.evalR)) :
    Lindeberg.var μ (T.evalR)
      ≤ ∑ e, revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (Lindeberg.coord e) := by
  
  have h1 := var_le_half_sum_step hpos hμ1 T
  rw [sum_step_eq_sum_edge T (T.evalR)] at h1
  refine h1.trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  
  calc (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
        Lindeberg.mean μ (fun ω => |adaptM μ T (T.evalR) (t + 1) ω - adaptM μ T (T.evalR) t ω|
            * freshAt T ω t e)
      ≤ (1 / 2) * ∑ t ∈ Finset.range (treeDepth T),
          2 * (Lindeberg.cov μ (T.evalR) (Lindeberg.coord e)
              * Lindeberg.mean μ (fun ω => freshAt T ω t e)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 2)
        exact Finset.sum_le_sum (fun t _ => hStep t e)
    _ = Lindeberg.cov μ (T.evalR) (Lindeberg.coord e) * ∑ t ∈ Finset.range (treeDepth T),
          Lindeberg.mean μ (fun ω => freshAt T ω t e) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ = revealmentMu μ T e * Lindeberg.cov μ (T.evalR) (Lindeberg.coord e) := by
        rw [revealmentMu_eq_sum]; ring










section FK

open StatMech.OSSS.MonotonicFK










theorem fk_q2_osss_sharp {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (T : DecisionTree (Sym2 V)) (hStep : StepCovBoundTwo (fkMass G p 2) T (T.evalR)) :
    Lindeberg.var (fkMass G p 2) (T.evalR)
      ≤ ∑ e, revealmentMu (fkMass G p 2) T e
          * Lindeberg.cov (fkMass G p 2) (T.evalR) (Lindeberg.coord e) :=
  tree_osss
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num)) T hStep

end FK

end AdaptiveTau

end OSSS

end StatMech
