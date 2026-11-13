/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.OSSS.FrontierFamilyClose
import Code.OSSS.AdaptiveCausalOSSS
import Code.FK.WiredDomChain

open scoped BigOperators
open MeasureTheory Filter Topology

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech
namespace OSSS
namespace FamilyEqzzzResolution

open FrontierFamilyClose LindebergTree Lindeberg
open StatMech.OSSS.DecisionTree
open StatMech.OSSS.MonotonicFK

variable {E : Type*} [Fintype E] [DecidableEq E]




def BareAdaptiveFamilyOSSS {μ : ConfigSpace E → ℝ} {κ : Type*}
    (Tf : κ → DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  ∀ k, Lindeberg.var μ f ≤
    ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e)




def AdaptiveFamilyOSSS {μ : ConfigSpace E → ℝ} {κ : Type*}
    (Tf : κ → DecisionTree E) (f : ConfigSpace E → ℝ) : Prop :=
  (∀ k, (Tf k).evalR = f) ∧ BareAdaptiveFamilyOSSS (μ := μ) Tf f



theorem adaptiveFamilyOSSS_of_causal {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {κ : Type*}
    (Tf : κ → DecisionTree E) {f : ConfigSpace E → ℝ}
    (hf : Monotone f) (hTf : ∀ k, (Tf k).evalR = f) :
    AdaptiveFamilyOSSS (μ := μ) Tf f := by
  refine ⟨hTf, ?_⟩
  intro k
  have hmono : Monotonic.IsMonotonicMeasure μ :=
    Monotonic.fkg_implies_monotonic hpos hFKG
  have hfT : Monotone (Tf k).evalR := by
    rw [hTf k]
    exact hf
  have h := AdaptiveCausalKernel.adaptive_tree_osss μ hpos hμ1 hmono (Tf k) hfT
  rw [hTf k] at h
  exact h




theorem bareAdaptiveFamilyOSSS_not_arbitrary :
    ¬ BareAdaptiveFamilyOSSS (μ := StepCov.Counterexample.muU)
      (fun _ : Unit => DecisionTree.leaf false) (Lindeberg.coord false) := by
  intro h
  have hvar :
      Lindeberg.var StepCov.Counterexample.muU (Lindeberg.coord false) = 1 / 4 := by
    unfold Lindeberg.var Lindeberg.cov Lindeberg.mean Lindeberg.coord
    unfold StepCov.Counterexample.muU
    rw [StepCov.Counterexample.sum_boolfun, StepCov.Counterexample.sum_boolfun]
    norm_num
  have hrev : ∀ e : Bool,
      revealmentMu StepCov.Counterexample.muU (DecisionTree.leaf false) e = 0 := by
    intro e
    unfold revealmentMu Lindeberg.mean
    simp [DecisionTree.queried]
  have hb := h ()
  simp_rw [hvar, hrev, zero_mul, Finset.sum_const_zero] at hb
  norm_num at hb




theorem var_le_avg_adaptive_reveal_mul_sum_cov {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {κ : Type*} [Fintype κ] [Nonempty κ]
    (Tf : κ → DecisionTree E) {f : ConfigSpace E → ℝ} (hf : Monotone f)
    (hOSSS : AdaptiveFamilyOSSS (μ := μ) Tf f) (D : ℝ)
    (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) *
      ∑ k, revealmentMu μ (Tf k) e ≤ D) :
    Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  have hκpos : (0 : ℝ) < (Fintype.card κ : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hcovnn : ∀ e, 0 ≤ Lindeberg.cov μ f (Lindeberg.coord e) :=
    fun e => cov_coord_nonneg hpos hμ1 hFKG hf e
  have havg : (Fintype.card κ : ℝ) * Lindeberg.var μ f ≤
      ∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e) := by
    have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hOSSS.2 k)
    rwa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hswap :
      (∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e)) =
        ∑ e, (∑ k, revealmentMu μ (Tf k) e) * Lindeberg.cov μ f (Lindeberg.coord e) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_mul]
  have hbnd :
      (∑ e, (∑ k, revealmentMu μ (Tf k) e) * Lindeberg.cov μ f (Lindeberg.coord e)) ≤
        ∑ e, ((Fintype.card κ : ℝ) * D) * Lindeberg.cov μ f (Lindeberg.coord e) := by
    apply Finset.sum_le_sum
    intro e _
    apply mul_le_mul_of_nonneg_right _ (hcovnn e)
    have he := hD e
    rw [one_div, inv_mul_le_iff₀ hκpos] at he
    exact he
  have hmain : (Fintype.card κ : ℝ) * Lindeberg.var μ f ≤
      (Fintype.card κ : ℝ) * (D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) := by
    calc
      (Fintype.card κ : ℝ) * Lindeberg.var μ f
          ≤ ∑ k, ∑ e, revealmentMu μ (Tf k) e * Lindeberg.cov μ f (Lindeberg.coord e) := havg
      _ = ∑ e, (∑ k, revealmentMu μ (Tf k) e) * Lindeberg.cov μ f (Lindeberg.coord e) := hswap
      _ ≤ ∑ e, ((Fintype.card κ : ℝ) * D) * Lindeberg.cov μ f (Lindeberg.coord e) := hbnd
      _ = (Fintype.card κ : ℝ) * (D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e)) := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.mul_sum]
  exact le_of_mul_le_mul_left hmain hκpos


theorem var_le_avg_adaptive_reveal_mul_sum_cov_unconditional
    {μ : ConfigSpace E → ℝ}
    (hpos : ∀ ω, 0 < μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (hFKG : FKGLatticeCondition μ) {κ : Type*} [Fintype κ] [Nonempty κ]
    (Tf : κ → DecisionTree E) {f : ConfigSpace E → ℝ} (hf : Monotone f)
    (hTf : ∀ k, (Tf k).evalR = f) (D : ℝ)
    (hD : ∀ e, (1 / (Fintype.card κ : ℝ)) *
      ∑ k, revealmentMu μ (Tf k) e ≤ D) :
    Lindeberg.var μ f ≤ D * ∑ e, Lindeberg.cov μ f (Lindeberg.coord e) := by
  exact var_le_avg_adaptive_reveal_mul_sum_cov hpos hμ1 hFKG Tf hf
    (adaptiveFamilyOSSS_of_causal hpos hμ1 hFKG Tf hf hTf) D hD




theorem fk_q2_cov_lower_bound_of_adaptive_family
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree (Sym2 W))
    {f : ConfigSpace (Sym2 W) → ℝ} (hf : Monotone f)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (hOSSS : AdaptiveFamilyOSSS (μ := fkMass G p 2) Tf f)
    (R : κ → Sym2 W → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealmentMu (fkMass G p 2) (Tf k) e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤
      ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  have hpos : ∀ ω, 0 < fkMass G p 2 ω :=
    fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 :=
    fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hFKG : FKGLatticeCondition (fkMass G p 2) :=
    FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num)
  have hvar : Lindeberg.var (fkMass G p 2) f =
      Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) :=
    RevealmentBoundAssembly.var_eq_theta_one_sub_theta hidem
  have hmain := var_le_avg_adaptive_reveal_mul_sum_cov hpos hμ1 hFKG Tf hf hOSSS D
    (frf_avg_treeReveal_le_of_perScale Tf R D hreach hsum)
  rw [hvar] at hmain
  rw [div_le_iff₀ hDpos]
  calc
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f)
        ≤ D * ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := hmain
    _ = (∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e)) * D := by ring



theorem fk_q2_cov_lower_bound_of_adaptive_family_unconditional
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {κ : Type*} [Fintype κ] [Nonempty κ] (Tf : κ → DecisionTree (Sym2 W))
    {f : ConfigSpace (Sym2 W) → ℝ} (hf : Monotone f)
    (hidem : ∀ ω, f ω * f ω = f ω)
    (hTf : ∀ k, (Tf k).evalR = f)
    (R : κ → Sym2 W → ℝ) (D : ℝ) (hDpos : 0 < D)
    (hreach : ∀ k e, revealmentMu (fkMass G p 2) (Tf k) e ≤ R k e)
    (hsum : ∀ e, (∑ k, R k e) ≤ (Fintype.card κ : ℝ) * D) :
    Lindeberg.mean (fkMass G p 2) f * (1 - Lindeberg.mean (fkMass G p 2) f) / D ≤
      ∑ e, Lindeberg.cov (fkMass G p 2) f (Lindeberg.coord e) := by
  have hpos : ∀ ω, 0 < fkMass G p 2 ω :=
    fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 :=
    fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hFKG : FKGLatticeCondition (fkMass G p 2) :=
    FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num)
  exact fk_q2_cov_lower_bound_of_adaptive_family G hp hp1 Tf hf hidem
    (adaptiveFamilyOSSS_of_causal hpos hμ1 hFKG Tf hf hTf)
    R D hDpos hreach hsum




theorem wired_box_theta_tendsto {d : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto
      (fun n => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
      atTop (nhds (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) :=
  FK.boxBoundaryConnProfile_tendsto hp hp1

end FamilyEqzzzResolution
end OSSS
end StatMech
