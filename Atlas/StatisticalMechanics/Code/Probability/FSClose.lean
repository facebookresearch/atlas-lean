/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.Probability.EntropySubadditivity
import Code.Probability.GlobalLSI

open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false

namespace StatMech.Probability

open StatMech StatMech.OSSS



variable {E : Type*} [Fintype E] [DecidableEq E]

omit [Fintype E] in











theorem fsc2_perCoord_lsi {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (G : ConfigSpace E → ℝ) (e : E) (ω : ConfigSpace E) :
    esd_entCoord p (fun ω => (G ω) ^ 2) e ω
      ≤ (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2 := by
  
  have heq : esd_entCoord p (fun ω => (G ω) ^ 2) e ω
      = tpl_ent p (G (StatMech.setClosed e ω) ^ 2) (G (StatMech.setOpen e ω) ^ 2) := by
    unfold esd_entCoord tpl_ent esd_Phi OSSS.condMean OSSS.bernoulliWeight
    simp only [if_true, Bool.false_eq_true, if_false]
    ring_nf
  rw [heq]
  have hlsi := tpl_lsi hp0 hp1 (G (StatMech.setClosed e ω)) (G (StatMech.setOpen e ω))
  
  rw [show (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2
      = (G (StatMech.setClosed e ω) - G (StatMech.setOpen e ω)) ^ 2 from by ring]
  exact hlsi












theorem fsc2_dirichlet_fourier_coord {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (G : ConfigSpace E → ℝ) (e : E) :
    OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2)
      = (1 / (ptn_sigma p) ^ 2) * ∑ S ∈ univ.filter (fun S : Finset E => e ∈ S),
          (ptn_coeff p G S) ^ 2 := by
  have hd : (fun ω : ConfigSpace E => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2)
      = (fun ω => (∑ S ∈ univ.filter (fun S => e ∈ S),
          (ptn_coeff p G S / ptn_sigma p) * ptn_pchar p (S.erase e) ω) ^ 2) := by
    funext ω; rw [ptn_deriv_fourier hp0 hp1 G e ω]
  rw [hd, ptn_expect_sum_pchar_sq hp0 hp1 _ _ (fun S => S.erase e) (ptn_erase_injOn e)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  rw [div_pow, one_div, ← div_eq_inv_mul]








theorem fsc2_dirichlet_fourier {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (G : ConfigSpace E → ℝ) :
    (∑ e : E, OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2))
      = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * (ptn_coeff p G S) ^ 2 := by
  set c := fun S : Finset E => (ptn_coeff p G S) ^ 2 with hc
  
  have hper : ∀ e : E, OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2)
      = (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (if e ∈ S then c S else 0) := by
    intro e
    rw [fsc2_dirichlet_fourier_coord hp0 hp1 G e, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun e _ => hper e)]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]



omit [Fintype E] in


theorem fsc2_reindex_setOpen {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : κ ≃ E) (e' : κ) (ω : ConfigSpace κ) :
    (fun i : E => StatMech.setOpen e' ω (σ.symm i))
      = StatMech.setOpen (σ e') (fun i : E => ω (σ.symm i)) := by
  funext i
  unfold StatMech.setOpen
  by_cases hi : i = σ e'
  · subst hi; rw [Equiv.symm_apply_apply, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne (by
      intro h; exact hi (by rw [← Equiv.apply_symm_apply σ i, h]))]

omit [Fintype E] in

theorem fsc2_reindex_setClosed {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : κ ≃ E) (e' : κ) (ω : ConfigSpace κ) :
    (fun i : E => StatMech.setClosed e' ω (σ.symm i))
      = StatMech.setClosed (σ e') (fun i : E => ω (σ.symm i)) := by
  funext i
  unfold StatMech.setClosed
  by_cases hi : i = σ e'
  · subst hi; rw [Equiv.symm_apply_apply, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hi, Function.update_of_ne (by
      intro h; exact hi (by rw [← Equiv.apply_symm_apply σ i, h]))]

omit [Fintype E] in



theorem fsc2_deriv_sq_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : κ ≃ E) (G : ConfigSpace E → ℝ) (e' : κ) :
    (fun ω : ConfigSpace κ => (ptn_reindex σ G (StatMech.setOpen e' ω)
        - ptn_reindex σ G (StatMech.setClosed e' ω)) ^ 2)
      = ptn_reindex σ (fun x => (G (StatMech.setOpen (σ e') x)
          - G (StatMech.setClosed (σ e') x)) ^ 2) := by
  funext ω
  unfold ptn_reindex
  rw [fsc2_reindex_setOpen σ e' ω, fsc2_reindex_setClosed σ e' ω]



theorem fsc2_dirichlet_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : κ ≃ E) (p : ℝ) (G : ConfigSpace E → ℝ) :
    (∑ e' : κ, OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (ptn_reindex σ G (StatMech.setOpen e' ω)
          - ptn_reindex σ G (StatMech.setClosed e' ω)) ^ 2))
      = ∑ e : E, OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2) := by
  rw [← Equiv.sum_comp σ (fun e : E => OSSS.expect (OSSS.bernoulliWeight p)
      (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2))]
  apply Finset.sum_congr rfl
  intro e' _
  rw [fsc2_deriv_sq_reindex σ G e', ptn_expect_reindex]




theorem fsc2_ent_reindex {κ : Type*} [Fintype κ] [DecidableEq κ]
    (σ : κ ≃ E) (p : ℝ) (G : ConfigSpace E → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (ptn_reindex σ G ω) ^ 2)
      = esd_ent (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2) := by
  unfold esd_ent
  have hPhi : OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => esd_Phi ((ptn_reindex σ G ω) ^ 2))
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => esd_Phi ((G ω) ^ 2)) := by
    rw [show (fun ω : ConfigSpace κ => esd_Phi ((ptn_reindex σ G ω) ^ 2))
        = ptn_reindex σ (fun x => esd_Phi ((G x) ^ 2)) from rfl, ptn_expect_reindex]
  have hMean : OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (ptn_reindex σ G ω) ^ 2)
      = OSSS.expect (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2) := by
    rw [show (fun ω : ConfigSpace κ => (ptn_reindex σ G ω) ^ 2)
        = ptn_reindex σ (fun x => (G x) ^ 2) from rfl, ptn_expect_reindex]
  rw [hPhi, hMean]










theorem fsc2_globalLSI {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (G : ConfigSpace E → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2)
      ≤ ∑ e : E, OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => (G (StatMech.setOpen e ω) - G (StatMech.setClosed e ω)) ^ 2) := by
  set σ : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm with hσ
  set H := ptn_reindex σ G with hH
  
  have hfin := gls_globalLSI hp0 hp1 H
  
  have hderiv : (∑ e' : Fin (Fintype.card E), OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => (gls_deriv H e' ω) ^ 2))
      = ∑ e' : Fin (Fintype.card E), OSSS.expect (OSSS.bernoulliWeight p)
          (fun ω => (H (StatMech.setOpen e' ω) - H (StatMech.setClosed e' ω)) ^ 2) := by
    apply Finset.sum_congr rfl; intro e' _; rfl
  rw [hderiv] at hfin
  
  rw [fsc2_ent_reindex σ p G] at hfin
  rw [hH, fsc2_dirichlet_reindex σ p G] at hfin
  exact hfin








theorem fsc2_lsi_spectral {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (G : ConfigSpace E → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (G ω) ^ 2)
      ≤ (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E, (S.card : ℝ) * (ptn_coeff p G S) ^ 2 := by
  refine (fsc2_globalLSI hp0 hp1 G).trans (le_of_eq ?_)
  exact fsc2_dirichlet_fourier hp0 hp1 G






theorem fsc2_coeff_noiseOp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ) (f : ConfigSpace E → ℝ)
    (S : Finset E) :
    ptn_coeff p (ptn_noiseOp p ρ f) S = ρ ^ S.card * ptn_coeff p f S := by
  unfold ptn_coeff ptn_noiseOp
  
  rw [show (fun ω : ConfigSpace E => (∑ T : Finset E, ρ ^ T.card * ptn_coeff p f T * ptn_pchar p T ω) * ptn_pchar p S ω)
      = (fun ω => ∑ T : Finset E, (ρ ^ T.card * ptn_coeff p f T) * (ptn_pchar p T ω * ptn_pchar p S ω))
    from by funext ω; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro T _; ring]
  rw [ptn_expect_finsetSum]
  have hterm : ∀ T ∈ (univ : Finset (Finset E)),
      OSSS.expect (OSSS.bernoulliWeight p)
        (fun ω => ρ ^ T.card * ptn_coeff p f T * (ptn_pchar p T ω * ptn_pchar p S ω))
        = ρ ^ T.card * ptn_coeff p f T * (if T = S then 1 else 0) := by
    intro T _; rw [OSSS.expect_const_mul, ptn_orthonormal hp0 hp1 T S]
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single_of_mem S (Finset.mem_univ S)]
  · rw [if_pos rfl, mul_one]; rfl
  · intro T _ hTS; rw [if_neg hTS, mul_zero]









theorem fsc2_lsi_spectral_noiseOp {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (ρ : ℝ)
    (f : ConfigSpace E → ℝ) :
    esd_ent (OSSS.bernoulliWeight p) (fun ω => (ptn_noiseOp p ρ f ω) ^ 2)
      ≤ (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E,
          (S.card : ℝ) * ((ρ ^ S.card) ^ 2 * (ptn_coeff p f S) ^ 2) := by
  refine (fsc2_lsi_spectral hp0 hp1 (ptn_noiseOp p ρ f)).trans (le_of_eq ?_)
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  rw [fsc2_coeff_noiseOp hp0 hp1 ρ f S]
  ring











def fsc2_EntMassFamily {E : Type} [Fintype E] [DecidableEq E] (p : ℝ) (φ : ConfigSpace E → Bool) : Prop :=
  ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    esd_ent (OSSS.bernoulliWeight p)
        (fun ω => (ptn_noiseOp p ρ (fun ω => if φ ω then (1 : ℝ) else 0) ω) ^ 2)
      ≤ (1 / (ptn_sigma p) ^ 2) * ∑ S : Finset E,
          (S.card : ℝ) * ((ρ ^ S.card) ^ 2 * (ptn_coeff p (fun ω => if φ ω then (1 : ℝ) else 0) S) ^ 2)





theorem fsc2_entMassFamily_holds {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] (φ : ConfigSpace E → Bool) :
    fsc2_EntMassFamily p φ :=
  fun ρ _ _ => fsc2_lsi_spectral_noiseOp hp0 hp1 ρ (fun ω => if φ ω then (1 : ℝ) else 0)






























def fsc2_DampingHardResidue (q : ℝ) : Prop :=
  ∀ p ∈ Set.Ioo (1 / 2 : ℝ) q, p < 1 → ∀ {E : Type} [Fintype E] [DecidableEq E] [Nonempty E]
    (φ : ConfigSpace E → Bool),
    0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) →
      0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) →
      maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        < Real.exp (-(1 / (2 * (p * (1 - p))))) →
      fsc2_EntMassFamily p φ →
        pen_dampedMass p (Real.exp (-(1 / (2 * (p * (1 - p)))))) (fun ω => if φ ω then (1 : ℝ) else 0)
          ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
            * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)

















theorem fsc2_dampingHard_of_residue {q : ℝ} (H : fsc2_DampingHardResidue q) :
    esa_DampingHard q := by
  intro p hp hp1 E _ _ _ φ hVar hδpos hδsmall
  have hp0 : 0 < p := by have := hp.1; linarith
  
  obtain ⟨hr0pos, hr0lt1, hr0bal⟩ := esa_logBalance_threshold hp0 hp1
  
  have hfam : fsc2_EntMassFamily p φ := fsc2_entMassFamily_holds hp0 hp1 φ
  
  have hDamp := H p hp hp1 φ hVar hδpos hδsmall hfam
  
  refine ⟨Real.exp (-(1 / (2 * (p * (1 - p))))), hr0pos, hr0lt1, hDamp, ?_⟩
  exact le_of_eq hr0bal





theorem fsc2_dampingWitness_of_residue {q : ℝ} (H : fsc2_DampingHardResidue q) :
    pen_DampingWitness q :=
  esa_dampingWitness_of_hard (fsc2_dampingHard_of_residue H)


theorem fsc2_rhoOptimise_of_residue {q : ℝ} (H : fsc2_DampingHardResidue q) :
    ptn_RhoOptimise q :=
  esa_rhoOptimise_of_hard (fsc2_dampingHard_of_residue H)



theorem fsc2_PBiasedHC_of_residue {q : ℝ} (hq : q ≤ 1) (H : fsc2_DampingHardResidue q) :
    kpb_PBiasedHC q :=
  esa_PBiasedHC_of_hard hq (fsc2_dampingHard_of_residue H)







theorem fsc2_residue_nonvac {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] (φ : ConfigSpace E → Bool) :
    fsc2_EntMassFamily p φ :=
  fsc2_entMassFamily_holds hp0 hp1 φ







theorem fsc2_residue_noncirc {q : ℝ} (H : fsc2_DampingHardResidue q) {p : ℝ}
    (hp : p ∈ Set.Ioo (1 / 2 : ℝ) q) (hp1 : p < 1)
    {E : Type} [Fintype E] [DecidableEq E] [Nonempty E] (φ : ConfigSpace E → Bool)
    (hVar : 0 < OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδpos : 0 < maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0))
    (hδsmall : maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
      < Real.exp (-(1 / (2 * (p * (1 - p))))))
    (hfam : fsc2_EntMassFamily p φ) :
    pen_dampedMass p (Real.exp (-(1 / (2 * (p * (1 - p)))))) (fun ω => if φ ω then (1 : ℝ) else 0)
      ≤ maxInfl (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0)
        * OSSS.var (OSSS.bernoulliWeight p) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  H p hp hp1 φ hVar hδpos hδsmall hfam

end StatMech.Probability
