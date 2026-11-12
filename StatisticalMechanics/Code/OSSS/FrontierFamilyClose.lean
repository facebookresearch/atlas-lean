/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Code.OSSS.PerScaleRevealmentClose
import Code.OSSS.QueriedCrossTreeClose
import Code.OSSS.LindebergTree
import Code.OSSS.RevealmentBoundAssembly

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace StatMech

namespace OSSS

namespace FrontierFamilyClose

open StatMech.OSSS
open StatMech.OSSS.RevealmentConstruction
open StatMech.OSSS.LindebergTree
open StatMech.OSSS.Lindeberg
open StatMech.OSSS.PrefixCoversClose
open StatMech.OSSS.ReachBoxCrossing
open StatMech.OSSS.ReachDomination
open StatMech.OSSS.PerScaleRevealmentClose
open StatMech.OSSS.MonotonicFK
open StatMech.Lattice
open DecisionTree
open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]
variable {V : Type*} [DecidableEq V]















theorem frf_familyFrontierConn_false {κ : Type*} {nE : ℕ} (σf : κ → (Fin nE ≃ E))
    (f : ConfigSpace E → ℝ) (endU endV : E → V) (B : κ → Set V)
    (k₀ : κ) {e₀ : E} (he₀ : ((σf k₀).symm e₀ : ℕ) = 0)
    (X : ConfigSpace E) (hnc : ∃ w, f w ≠ f X)
    (hnotU : ¬ ConnOpenSet endU endV X (endU e₀) (B k₀))
    (hnotV : ¬ ConnOpenSet endU endV X (endV e₀) (B k₀)) :
    ¬ psr_FamilyFrontierConn σf f endU endV B := by
  intro hfam
  exact psr_frontierConn_first_refutable (σf k₀) f endU endV (B k₀) he₀ X hnc hnotU hnotV
    (hfam k₀ e₀)








theorem frf_familyFrontierConn_false_concrete {κ : Type*} (σf : κ → (Fin 3 ≃ Fin 3))
    (k₀ : κ) (hk₀ : ((σf k₀).symm 0 : ℕ) = 0) :
    ¬ psr_FamilyFrontierConn σf
        (indicatorConn psr_witnessEndU psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4)))
        psr_witnessEndU psr_witnessEndV (fun _ => ({0} : Set (Fin 4))) := by
  intro hfam
  exact psr_frontierConn_first_false_concrete (σf k₀) hk₀ (hfam k₀ 0)

















theorem frf_mean_reveal_le_of_queried_imp_or {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (T : DecisionTree E) (e : E) (P Q : ConfigSpace E → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ ω, e ∈ T.queried ω → P ω ∨ Q ω) :
    revealmentMu μ T e
      ≤ Lindeberg.mean μ (fun ω => if P ω then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun ω => if Q ω then (1 : ℝ) else 0) := by
  unfold revealmentMu Lindeberg.mean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  simp only []
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (hμ0 ω)
  by_cases hq : e ∈ T.queried ω
  · rw [if_pos hq]
    rcases h ω hq with hP | hQ
    · rw [if_pos hP]
      have : (0 : ℝ) ≤ if Q ω then (1 : ℝ) else 0 := by split <;> norm_num
      linarith
    · rw [if_pos hQ]
      have : (0 : ℝ) ≤ if P ω then (1 : ℝ) else 0 := by split <;> norm_num
      linarith
  · rw [if_neg hq]
    have h1 : (0 : ℝ) ≤ if P ω then (1 : ℝ) else 0 := by split <;> norm_num
    have h2 : (0 : ℝ) ≤ if Q ω then (1 : ℝ) else 0 := by split <;> norm_num
    linarith












theorem frf_mean_reveal_crossTree_le_connOpen {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (endU endV : E → V) (o : V) (B C : Set V) (l : List E) (disc₀ : Finset V)
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ B) (i : E)
    [DecidablePred (fun ω => ConnOpenSet endU endV ω (endU i) B)]
    [DecidablePred (fun ω => ConnOpenSet endU endV ω (endV i) B)] :
    revealmentMu μ (crossTree endU endV o C l disc₀) i
      ≤ Lindeberg.mean μ (fun ω => if ConnOpenSet endU endV ω (endU i) B then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun ω => if ConnOpenSet endU endV ω (endV i) B then (1 : ℝ) else 0) :=
  frf_mean_reveal_le_of_queried_imp_or hμ0 (crossTree endU endV o C l disc₀) i
    (fun ω => ConnOpenSet endU endV ω (endU i) B)
    (fun ω => ConnOpenSet endU endV ω (endV i) B)
    (fun ω hq => incidentCluster_of_queried_crossTree endU endV o B C l disc₀ hdisc₀ ω i hq)

section Lattice

variable {d : ℕ}












theorem frf_mean_reveal_crossTree_le_connBox {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (C : Set (Site d)) (k : ℕ) (l : List E) (disc₀ : Finset (Site d))
    (hdisc₀ : ∀ x ∈ disc₀, x ∈ vertexBoundary d k) (i : E)
    [DecidablePred (fun ω => ConnOpenSet endU endV ω (endU i) (vertexBoundary d k))]
    [DecidablePred (fun ω => ConnOpenSet endU endV ω (endV i) (vertexBoundary d k))]
    [DecidablePred (fun ω => ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k))]
    [DecidablePred (fun ω => ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k))] :
    revealmentMu μ (crossTree endU endV o C l disc₀) i
      ≤ Lindeberg.mean μ
          (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU i) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV i) (vertexBoundary d k)
                    then (1 : ℝ) else 0) := by
  refine (frf_mean_reveal_crossTree_le_connOpen hμ0 endU endV o (vertexBoundary d k) C l disc₀
    hdisc₀ i).trans ?_
  apply add_le_add
  · exact mean_indicator_mono hμ0 _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact mean_indicator_mono hμ0 _ _
      (fun ω hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)

end Lattice






















theorem frf_var_le_avg_treeReveal_mul_sum_cov {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ)
    {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree E)
    {f : ConfigSpace E → ℝ} (hf : Monotone f) (hTf : ∀ k, (Tf k).evalR = f)
    (hStep : ∀ k, StepCovBound μ (Tf k) f) (D : ℝ)
    (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ D) :
    Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hcovnn : ∀ e, 0 ≤ Lindeberg.cov μ f (Lindeberg.coord e) :=
    fun e => cov_coord_nonneg hpos hμ1 hFKG hf e
  
  have hbound : ∀ k, Lindeberg.var μ f
      ≤ ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e) := by
    intro k
    have h := tree_osss hpos hμ1 (Tf k) (by rw [hTf k]; exact hStep k)
    rw [hTf k] at h
    exact h
  
  have havg : (Fintype.card κ : ℝ) * Lindeberg.var μ f
      ≤ ∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e) := by
    have hsum : ∑ _k : κ, Lindeberg.var μ f
        ≤ ∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e) :=
      Finset.sum_le_sum (fun k _ => hbound k)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  
  have hswap : ∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e)
      = ∑ e, (∑ k, revealmentMu μ (Tf k) e) * Lindeberg.cov μ f (Lindeberg.coord e) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _; rw [Finset.sum_mul]
  
  have hbnd : ∑ e, (∑ k, revealmentMu μ (Tf k) e) * Lindeberg.cov μ f (Lindeberg.coord e)
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
        ≤ ∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e) := havg
      _ = ∑ e, (∑ k, revealmentMu μ (Tf k) e) * Lindeberg.cov μ f (Lindeberg.coord e) := hswap
      _ ≤ ∑ e, ((Fintype.card κ : ℝ) * D) * Lindeberg.cov μ f (Lindeberg.coord e) := hbnd
      _ = ((Fintype.card κ : ℝ) * D) * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
            rw [Finset.mul_sum]
  have h2 : (Fintype.card κ : ℝ) * Lindeberg.var μ f
      ≤ (Fintype.card κ : ℝ) * (D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) := by
    calc (Fintype.card κ : ℝ) * Lindeberg.var μ f
        ≤ ((Fintype.card κ : ℝ) * D) * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := hcomb
      _ = (Fintype.card κ : ℝ) * (D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) := by ring
  exact le_of_mul_le_mul_left h2 hκpos





theorem frf_avg_treeReveal_le_of_perScale {μ : ConfigSpace E → ℝ}
    {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree E)
    (R : κ → E → ℝ) (D : ℝ)
    (hreach : ∀ k e, revealmentMu μ (Tf k) e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    ∀ e, (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ D := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  intro e
  rw [one_div, inv_mul_le_iff₀ hκpos]
  calc ∑ k, revealmentMu μ (Tf k) e
      ≤ ∑ k, R k e := Finset.sum_le_sum (fun k _ => hreach k e)
    _ ≤ (Fintype.card κ : ℝ) * D := hsum e










section FKResidue

variable {W : Type*} [Fintype W] [DecidableEq W]















theorem frf_fk_q2_cov_lower_bound_of_adaptiveFamily
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree (Sym2 W))
    {f : ConfigSpace (Sym2 W) → ℝ} (hf : Monotone f)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (hTf : ∀ k, (Tf k).evalR = f)
    (hStep : ∀ k, StepCovBound (fkMass G p 2) (Tf k) f)
    (R : κ → Sym2 W → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealmentMu (fkMass G p 2) (Tf k) e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  have hpos : ∀ ω, 0 < fkMass G p 2 ω := fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 := fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hFKG : FKGLatticeCondition (fkMass G p 2) :=
    FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num)
  have hvar : Lindeberg.var (fkMass G p 2) f
      = Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  have hmain := frf_var_le_avg_treeReveal_mul_sum_cov hpos hμ1 hFKG Tf hf hTf hStep D
    (frf_avg_treeReveal_le_of_perScale Tf R D hreach hsum)
  rw [hvar] at hmain
  rw [div_le_iff₀ hDpos]
  calc Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f)
      ≤ D * ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := hmain
    _ = (∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e)) * D := by ring

end FKResidue










theorem frf_revealmentMu_le_one {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (T : DecisionTree E) (e : E) :
    revealmentMu μ T e ≤ 1 := by
  unfold revealmentMu Lindeberg.mean
  calc ∑ ω, (if e ∈ T.queried ω then (1 : ℝ) else 0) * μ ω
      ≤ ∑ ω, (1 : ℝ) * μ ω := by
        apply Finset.sum_le_sum
        intro ω _
        apply mul_le_mul_of_nonneg_right _ (hμ0 ω)
        split <;> norm_num
    _ = 1 := by simp only [one_mul]; exact hμ1



theorem frf_avg_treeReveal_le_one {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree E)
    (e : E) :
    (1 / (Fintype.card κ : ℝ)) * ∑ k, revealmentMu μ (Tf k) e ≤ 1 := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [one_div, inv_mul_le_iff₀ hκpos, mul_one]
  calc ∑ k, revealmentMu μ (Tf k) e
      ≤ ∑ _k : κ, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => frf_revealmentMu_le_one hμ0 hμ1 (Tf k) e)
    _ = (Fintype.card κ : ℝ) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]







theorem frf_fk_q2_cov_lower_bound_adaptive_poincare {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree (Sym2 W))
    {f : ConfigSpace (Sym2 W) → ℝ} (hf : Monotone f)
    (hTf : ∀ k, (Tf k).evalR = f)
    (hStep : ∀ k, StepCovBound (fkMass G p 2) (Tf k) f) :
    Lindeberg.var (fkMass G p 2) f
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  have hpos : ∀ ω, 0 < fkMass G p 2 ω := fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 := fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hFKG : FKGLatticeCondition (fkMass G p 2) :=
    FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num)
  have h := frf_var_le_avg_treeReveal_mul_sum_cov hpos hμ1 hFKG Tf hf hTf hStep 1
    (fun e => frf_avg_treeReveal_le_one (fun ω => (hpos ω).le) hμ1 Tf e)
  simpa using h

end FrontierFamilyClose

end OSSS

end StatMech
