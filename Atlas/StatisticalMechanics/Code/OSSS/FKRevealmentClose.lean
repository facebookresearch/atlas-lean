/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































import Code.OSSS.RevealmentBoundAssembly
import Code.OSSS.RevealmentBoxCrossing
import Code.OSSS.RevealmentSum

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace FKRevealmentClose

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.AdaptDisintegration
open StatMech.OSSS.RevealmentBoxCrossing

variable {E : Type*} [Fintype E] [DecidableEq E]
























theorem var_le_avg_reveal_mul_sum_cov {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ E))
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (D : ℝ)
    (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ D) :
    Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcovnn : ∀ e, 0 ≤ Lindeberg.cov μ f (Lindeberg.coord e) :=
    fun e => LindebergTree.cov_coord_nonneg hpos hμ1 hFKG hf e
  
  have hbound : ∀ k, Lindeberg.var μ f
      ≤ ∑ e, revealAdapt μ (σf k) f e * Lindeberg.cov μ f (Lindeberg.coord e) :=
    fun k => osss_monotone_sharp hpos hμ1 hmono (σf k) hf hf0 hf1
  
  have havg : (Fintype.card κ : ℝ) * Lindeberg.var μ f
      ≤ ∑ k, ∑ e, revealAdapt μ (σf k) f e * Lindeberg.cov μ f (Lindeberg.coord e) := by
    have hsum : ∑ _k : κ, Lindeberg.var μ f
        ≤ ∑ k, ∑ e, revealAdapt μ (σf k) f e * Lindeberg.cov μ f (Lindeberg.coord e) :=
      Finset.sum_le_sum (fun k _ => hbound k)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  
  have hswap : ∑ k, ∑ e, revealAdapt μ (σf k) f e * Lindeberg.cov μ f (Lindeberg.coord e)
      = ∑ e, (∑ k, revealAdapt μ (σf k) f e) * Lindeberg.cov μ f (Lindeberg.coord e) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _; rw [Finset.sum_mul]
  
  have hbnd : ∑ e, (∑ k, revealAdapt μ (σf k) f e) * Lindeberg.cov μ f (Lindeberg.coord e)
      ≤ ∑ e, ((Fintype.card κ : ℝ) * D) * Lindeberg.cov μ f (Lindeberg.coord e) := by
    apply Finset.sum_le_sum
    intro e _
    apply mul_le_mul_of_nonneg_right _ (hcovnn e)
    have := hD e
    rw [one_div, inv_mul_le_iff₀ hκpos] at this
    linarith [this]
  
  have hcomb : (Fintype.card κ : ℝ) * Lindeberg.var μ f
      ≤ ((Fintype.card κ : ℝ) * D) * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
    calc (Fintype.card κ : ℝ) * Lindeberg.var μ f
        ≤ ∑ k, ∑ e, revealAdapt μ (σf k) f e * Lindeberg.cov μ f (Lindeberg.coord e) := havg
      _ = ∑ e, (∑ k, revealAdapt μ (σf k) f e) * Lindeberg.cov μ f (Lindeberg.coord e) := hswap
      _ ≤ ∑ e, ((Fintype.card κ : ℝ) * D) * Lindeberg.cov μ f (Lindeberg.coord e) := hbnd
      _ = ((Fintype.card κ : ℝ) * D) * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
            rw [Finset.mul_sum]
  
  have hfinal : Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
    have h2 : (Fintype.card κ : ℝ) * Lindeberg.var μ f
        ≤ (Fintype.card κ : ℝ) * (D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) := by
      calc (Fintype.card κ : ℝ) * Lindeberg.var μ f
          ≤ ((Fintype.card κ : ℝ) * D) * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := hcomb
        _ = (Fintype.card κ : ℝ) * (D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) := by ring
    exact le_of_mul_le_mul_left h2 hκpos
  exact hfinal





















theorem fk_os_cov_lower_bound_avg {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ E))
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (D : ℝ) (hDpos : 0 < D)
    (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hvar : Lindeberg.var μ f = Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  have hmain := var_le_avg_reveal_mul_sum_cov hpos hμ1 hFKG hmono σf hf hf0 hf1 D hD
  rw [hvar] at hmain
  rw [div_le_iff₀ hDpos]
  calc Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)
      ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := hmain
    _ = (∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) * D := by ring

















theorem avg_reveal_le_of_perScale {μ : ConfigSpace E → ℝ}
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ E))
    (f : ConfigSpace E → ℝ) (R : κ → E → ℝ) (D : ℝ)
    (hreach : ∀ k e, revealAdapt μ (σf k) f e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ D := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  intro e
  rw [one_div, inv_mul_le_iff₀ hκpos]
  calc ∑ k, revealAdapt μ (σf k) f e
      ≤ ∑ k, R k e := Finset.sum_le_sum (fun k _ => hreach k e)
    _ ≤ (Fintype.card κ : ℝ) * D := hsum e
















theorem fk_os_cov_lower_bound_from_perScaleReveal {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    (hmono : IsMonotonicMeasure μ)
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ E))
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (R : κ → E → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealAdapt μ (σf k) f e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) :=
  fk_os_cov_lower_bound_avg hpos hμ1 hFKG hmono σf hf hf0 hf1 hidem D hDpos
    (avg_reveal_le_of_perScale σf f R D hreach hsum)



















theorem revealAdapt_first_eq_one {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E)
    (he : (σ.symm e : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X) :
    revealAdapt μ σ f e = 1 := by
  rw [revealAdapt_eq_reachProb hpos hμ1 σ f e]
  unfold reachProb Lindeberg.mean
  rw [he]
  have hpref : OSSS.Coding.prefixSet (σ : Fin n → E) 0 = ∅ := by
    unfold OSSS.Coding.prefixSet; rw [OSSS.Coding.prefixIdx_zero]; simp
  have hcalc : ∀ X, reachInd σ f 0 X = 1 := by
    intro X
    unfold reachInd
    rw [if_neg]
    intro hdet
    exact hnc X (fun w => hdet w (by rw [hpref]; intro a ha; simp at ha))
  calc ∑ X, reachInd σ f 0 X * μ X = ∑ X, (1 : ℝ) * μ X := by
        apply Finset.sum_congr rfl; intro X _; rw [hcalc X]
    _ = 1 := by simp only [one_mul]; exact hμ1











theorem revealAdapt_single_no_over_n {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E)
    (he : (σ.symm e : ℕ) = 0) (hnc : ∀ X, ¬ ∀ w, f w = f X)
    {c : ℝ} (hc : c < 1) :
    ¬ revealAdapt μ σ f e ≤ c := by
  rw [revealAdapt_first_eq_one hpos hμ1 σ f e he hnc]
  intro h
  exact absurd (lt_of_le_of_lt h hc) (by norm_num)








theorem revealAdapt_eq_one_witness :
    revealAdapt (fun _ : ConfigSpace (Fin 2) => 1 / (Fintype.card (ConfigSpace (Fin 2)) : ℝ))
      (Equiv.refl (Fin 2)) (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) = 1 := by
  have hcard : (0 : ℝ) < (Fintype.card (ConfigSpace (Fin 2)) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  refine revealAdapt_first_eq_one (fun _ => by positivity) ?_ (Equiv.refl (Fin 2))
    (Lindeberg.coord (0 : Fin 2)) (0 : Fin 2) (by simp) ?_
  · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div, div_self hcard.ne']
  · intro X hall
    have h1 := hall (fun _ => true)
    have h0 := hall (fun _ => false)
    unfold Lindeberg.coord at h1 h0
    rw [if_pos rfl] at h1
    rw [if_neg (by decide)] at h0
    
    rw [← h0] at h1
    exact absurd h1 (by norm_num)











theorem avg_reveal_le_one {μ : ConfigSpace E → ℝ}
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ E))
    (f : ConfigSpace E → ℝ) (e : E) :
    (1 / (Fintype.card κ : ℝ)) * ∑ k, revealAdapt μ (σf k) f e ≤ 1 := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [one_div, inv_mul_le_iff₀ hκpos, mul_one]
  calc ∑ k, revealAdapt μ (σf k) f e
      ≤ ∑ _k : κ, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => RevealmentBoundAssembly.revealAdapt_le_one μ (σf k) f e)
    _ = (Fintype.card κ : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]










theorem fk_os_cov_lower_bound_avg_poincare {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ E))
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f)
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have h := fk_os_cov_lower_bound_avg hpos hμ1 hFKG hmono σf hf hf0 hf1 hidem
    1 (by norm_num) (fun e => avg_reveal_le_one σf f e)
  simpa using h









section FK

variable {V : Type*} [Fintype V] [DecidableEq V]


















theorem fk_q2_cov_lower_bound_from_perScaleReveal
    (G : SimpleGraph V) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] {m : ℕ} (σf : κ → (Fin m ≃ Sym2 V))
    {f : ConfigSpace (Sym2 V) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (R : κ → Sym2 V → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealAdapt (fkMass G p 2) (σf k) f e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) :=
  fk_os_cov_lower_bound_from_perScaleReveal
    (fun ω => fkMass_pos G hp hp1 (by norm_num) ω)
    (fkMass_sum_eq_one G hp hp1 (by norm_num))
    (FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num))
    (fkMass_isMonotonic G hp hp1 (by norm_num)) σf hf hf0 hf1 hidem R D hDpos hreach hsum

end FK

end FKRevealmentClose

end OSSS

end StatMech
