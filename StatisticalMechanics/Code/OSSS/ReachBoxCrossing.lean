/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Code.OSSS.RevealmentBoxCrossing
import Code.OSSS.RevealmentCrossBox

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false

namespace StatMech

namespace OSSS

namespace ReachBoxCrossing

open OSSS.Monotonic OSSS.AdaptMConditional StatMech.Probability
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.AdaptDisintegration
open OSSS.GrandCoupling OSSS.Coding
open StatMech.OSSS.RevealmentBoundAssembly
open StatMech.OSSS.RevealmentBoxCrossing
open StatMech.OSSS.RevealmentConstruction
open StatMech.Lattice

variable {E : Type*} [Fintype E] [DecidableEq E]










theorem mean_indicator_le {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (g : ConfigSpace E → ℝ) (P : ConfigSpace E → Prop) [DecidablePred P]
    (hg : ∀ X, g X ≤ if P X then (1 : ℝ) else 0) :
    Lindeberg.mean μ g
      ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) := by
  unfold Lindeberg.mean
  apply Finset.sum_le_sum
  intro X _
  exact mul_le_mul_of_nonneg_right (hg X) (hμ0 X)





theorem reachProb_le_of_undet_imp {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E)
    (P : ConfigSpace E → Prop) [DecidablePred P]
    (h : ∀ X, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) → P X) :
    reachProb μ σ f e ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0) := by
  unfold reachProb
  apply mean_indicator_le hμ0
  intro X
  unfold reachInd
  by_cases hdet : detAtC (σ : Fin n → E) f X (σ.symm e : ℕ)
  · rw [if_pos hdet]; split <;> norm_num
  · rw [if_neg hdet, if_pos (h X hdet)]








theorem mean_indicator_or_le {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q] :
    Lindeberg.mean μ (fun X => if P X ∨ Q X then (1 : ℝ) else 0)
      ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) := by
  unfold Lindeberg.mean
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro X _
  simp only []
  have hPnonNeg : (0 : ℝ) ≤ if P X then (1 : ℝ) else 0 := by split <;> norm_num
  have hQnonNeg : (0 : ℝ) ≤ if Q X then (1 : ℝ) else 0 := by split <;> norm_num
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (hμ0 X)
  by_cases hPQ : P X ∨ Q X
  · rw [if_pos hPQ]
    rcases hPQ with hP | hQ
    · rw [if_pos hP]; linarith
    · rw [if_pos hQ]; linarith
  · rw [if_neg hPQ]; linarith








theorem reachProb_le_of_undet_imp_or {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (e : E)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ X, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) → P X ∨ Q X) :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) :=
  (reachProb_le_of_undet_imp hμ0 σ f e (fun X => P X ∨ Q X) h).trans
    (mean_indicator_or_le hμ0 P Q)











variable {V : Type*} [DecidableEq V]







def FrontierConn {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (endU endV : E → V)
    (B : Set V) (e : E) : Prop :=
  ∀ X : ConfigSpace E, ¬ detAtC (σ : Fin n → E) f X (σ.symm e : ℕ) →
    ConnOpenSet endU endV X (endU e) B ∨ ConnOpenSet endU endV X (endV e) B







theorem reachProb_le_connOpen {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (endU endV : E → V) (B : Set V)
    (e : E) (hfront : FrontierConn σ f endU endV B e)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) B)]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) B)] :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endU e) B then (1 : ℝ) else 0)
        + Lindeberg.mean μ (fun X => if ConnOpenSet endU endV X (endV e) B then (1 : ℝ) else 0) :=
  reachProb_le_of_undet_imp_or hμ0 σ f e
    (fun X => ConnOpenSet endU endV X (endU e) B)
    (fun X => ConnOpenSet endU endV X (endV e) B)
    hfront








section Lattice

variable {d : ℕ}


theorem mean_indicator_mono {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    (P Q : ConfigSpace E → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ X, P X → Q X) :
    Lindeberg.mean μ (fun X => if P X then (1 : ℝ) else 0)
      ≤ Lindeberg.mean μ (fun X => if Q X then (1 : ℝ) else 0) := by
  unfold Lindeberg.mean
  apply Finset.sum_le_sum
  intro X _
  simp only []
  apply mul_le_mul_of_nonneg_right _ (hμ0 X)
  by_cases hP : P X
  · rw [if_pos hP, if_pos (h X hP)]
  · rw [if_neg hP]; split <;> norm_num













theorem reachProb_le_connBox {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (e : E)
    (hfront : FrontierConn σ f endU endV (vertexBoundary d k) e)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) := by
  refine (reachProb_le_connOpen hμ0 σ f endU endV (vertexBoundary d k) e hfront).trans ?_
  apply add_le_add
  · exact mean_indicator_mono hμ0 _ _
      (fun X hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)
  · exact mean_indicator_mono hμ0 _ _
      (fun X hP => connOpenSet_imp_connectedToSet hinj hcoh hadj hP)

















theorem revealAdapt_le_connBox {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (e : E)
    (hfront : FrontierConn σ f endU endV (vertexBoundary d k) e)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [DecidablePred (fun X => ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))] :
    revealAdapt μ σ f e
      ≤ Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) := by
  rw [revealAdapt_eq_reachProb hpos hμ1 σ f e]
  exact reachProb_le_connBox (fun ω => le_of_lt (hpos ω)) σ f hinj hcoh hadj k e hfront





















theorem os_cov_lower_bound_from_box_crossing {μ : ConfigSpace E → ℝ} (hpos : ∀ ω, 0 < μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (hFKG : FKGLatticeCondition μ) (hmono : IsMonotonicMeasure μ)
    {n : ℕ} (σ : Fin n ≃ E) {f : ConfigSpace E → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) (hidem : ∀ ω, f ω * f ω = f ω)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (k : ℕ) (D : ℝ) (hDpos : 0 < D)
    [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnOpenSet endU endV X (endU e) (vertexBoundary d k))]
    [∀ e X, Decidable (ConnOpenSet endU endV X (endV e) (vertexBoundary d k))]
    (hfront : ∀ e, FrontierConn σ f endU endV (vertexBoundary d k) e)
    (hbox : ∀ e,
      Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnectedToSet d (liftCfg edge X) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0) ≤ D) :
    Lindeberg.mean μ f * (1 - Lindeberg.mean μ f) / D
      ≤ ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  refine os_cov_lower_bound_assembled hpos hμ1 hFKG hmono σ hf hf0 hf1 hidem D hDpos
    (fun e => ?_)
  exact (revealAdapt_le_connBox hpos hμ1 σ f hinj hcoh hadj k e (hfront e)).trans (hbox e)

end Lattice










variable {V : Type*} [DecidableEq V]




theorem frontierConn_univ {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ)
    (endU endV : E → V) (e : E) :
    FrontierConn σ f endU endV (Set.univ : Set V) e := by
  intro X _
  exact Or.inl (connOpenSet_of_mem (Set.mem_univ _))






theorem frontierConn_satisfiable {μ : ConfigSpace E → ℝ} (hμ0 : ∀ ω, 0 ≤ μ ω)
    {n : ℕ} (σ : Fin n ≃ E) (f : ConfigSpace E → ℝ) (endU endV : E → V) (e : E)
    [DecidablePred (fun X => ConnOpenSet endU endV X (endU e) (Set.univ : Set V))]
    [DecidablePred (fun X => ConnOpenSet endU endV X (endV e) (Set.univ : Set V))] :
    reachProb μ σ f e
      ≤ Lindeberg.mean μ
          (fun X => if ConnOpenSet endU endV X (endU e) (Set.univ : Set V) then (1 : ℝ) else 0)
        + Lindeberg.mean μ
          (fun X => if ConnOpenSet endU endV X (endV e) (Set.univ : Set V) then (1 : ℝ) else 0) :=
  reachProb_le_connOpen hμ0 σ f endU endV Set.univ e (frontierConn_univ σ f endU endV e)

end ReachBoxCrossing

end OSSS

end StatMech
