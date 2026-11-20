/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Code.OSSS.FamilyEqzzzResolution
import Code.OSSS.RevealmentSum

open scoped BigOperators
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false

namespace StatMech

namespace OSSS

namespace AdaptiveCovLowerClose

open StatMech.OSSS
open StatMech.OSSS.LindebergTree
open StatMech.OSSS.Lindeberg
open StatMech.OSSS.FrontierFamilyClose
open StatMech.OSSS.FamilyEqzzzResolution
open StatMech.OSSS.MonotonicFK
open StatMech.OSSS.RevealmentConstruction
open StatMech.Lattice
open DecisionTree
open scoped Classical

variable {d : ℕ}
variable {W : Type*} [Fintype W] [DecidableEq W]










noncomputable def crossInd (edge : Sym2 W → Sym2 (Site d)) (o : Site d) (n : ℕ) :
    ConfigSpace (Sym2 W) → ℝ :=
  (crossEvent edge o (vertexBoundary d n)).indicator (fun _ => (1 : ℝ))



noncomputable def boxReveal (μ : ConfigSpace (Sym2 W) → ℝ)
    (edge : Sym2 W → Sym2 (Site d)) (endU endV : Sym2 W → Site d)
    (k : ℕ) (e : Sym2 W) : ℝ :=
  Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                then (1 : ℝ) else 0)
    + Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0)






























theorem acl_fk_q2_hcov_crossTree
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {edge : Sym2 W → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : Sym2 W → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List (Sym2 W)) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (D : ℝ) (hDpos : 0 < D)
    (hsum : ∀ e : Sym2 W,
      (∑ k : ↥(Finset.Icc 1 n),
        boxReveal (fkMass G p 2) edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D) :
    Lindeberg.mean (fkMass G p 2) (crossInd edge o n)
        * (1 - Lindeberg.mean (fkMass G p 2) (crossInd edge o n)) / D
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
  classical
  haveI hne : Nonempty (↥(Finset.Icc 1 n)) :=
    ⟨⟨1, by rw [Finset.mem_Icc]; exact ⟨le_refl 1, hn⟩⟩⟩
  set μ := fkMass G p 2 with hμdef
  set f : ConfigSpace (Sym2 W) → ℝ := crossInd edge o n with hf0
  set Tf : ↥(Finset.Icc 1 n) → DecisionTree (Sym2 W) :=
    fun k => crossTree endU endV o (vertexBoundary d n) l (disc₀ (k : ℕ)) with hTfdef
  set R : ↥(Finset.Icc 1 n) → Sym2 W → ℝ :=
    fun k e => boxReveal μ edge endU endV (k : ℕ) e with hRdef
  have hpos : ∀ ω, 0 < μ ω := fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  
  have hf : Monotone f := by
    rw [hf0, crossInd]
    exact (connectedToSet_increasing edge o (vertexBoundary d n)).indicator_monotone
  
  have hidem : ∀ ω, f ω * f ω = f ω := by
    intro ω; rw [hf0, crossInd, Set.indicator_apply]; split_ifs <;> norm_num
  
  have hTf : ∀ k, (Tf k).evalR = f := by
    intro k
    funext ω
    have hk1 : 1 ≤ (k : ℕ) := (Finset.mem_Icc.mp k.2).1
    have hkn : (k : ℕ) ≤ n := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree_connected (E := Sym2 W) (d := d) hinj hcoh hadj
      (k : ℕ) n hk1 hkn o (ho (k : ℕ) hk1) l hl (disc₀ (k : ℕ))
      (hdisc₀sup (k : ℕ)) (hoB (k : ℕ)) ω
    rw [hTfdef, heval, hf0, crossInd]
    by_cases hconn : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
    · have hmem : ω ∈ crossEvent edge o (vertexBoundary d n) := hconn
      rw [if_pos hconn, Set.indicator_of_mem hmem]
    · have hmem : ω ∉ crossEvent edge o (vertexBoundary d n) := hconn
      rw [if_neg hconn, Set.indicator_of_notMem hmem]
  
  have hreach : ∀ k e, revealmentMu μ (Tf k) e ≤ R k e := by
    intro k e
    rw [hTfdef, hRdef]
    simp only [boxReveal]
    exact frf_mean_reveal_crossTree_le_connBox (μ := μ) (fun ω => (hpos ω).le)
      hinj hcoh hadj o (vertexBoundary d n) (k : ℕ) l (disc₀ (k : ℕ))
      (hdisc₀sub (k : ℕ)) e
  
  have hsum' : ∀ e, (∑ k, R k e) ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D := by
    intro e; rw [hRdef]; exact hsum e
  
  exact fk_q2_cov_lower_bound_of_adaptive_family_unconditional G hp hp1 Tf hf hidem hTf
    R D hDpos hreach hsum'




















theorem acl_boxReveal_sum_le
    {μ : ConfigSpace (Sym2 W) → ℝ}
    {edge : Sym2 W → Sym2 (Site d)} {endU endV : Sym2 W → Site d}
    (n : ℕ) (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (conn : Site d → ℕ → ℝ) (hconnnn : ∀ x j, 0 ≤ conn x j)
    (e : Sym2 W) (ru rv : ℕ) (hru : ru ≤ n) (hrv : rv ≤ n)
    (hu : endU e ∈ Λ) (hv : endV e ∈ Λ)
    (hcompu : ∀ k,
      Lindeberg.mean μ
        (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                  then (1 : ℝ) else 0)
        ≤ conn (endU e) ((k : ℤ) - (ru : ℤ)).natAbs)
    (hcompv : ∀ k,
      Lindeberg.mean μ
        (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                  then (1 : ℝ) else 0)
        ≤ conn (endV e) ((k : ℤ) - (rv : ℤ)).natAbs) :
    (∑ k : ↥(Finset.Icc 1 n), boxReveal μ edge endU endV (k : ℕ) e)
      ≤ 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j) := by
  rw [Finset.sum_coe_sort (Finset.Icc 1 n)
    (fun k => boxReveal μ edge endU endV k e)]
  simp only [boxReveal]
  exact revealment_family_sum_le Λ hne conn hconnnn n ru rv hru hrv (endU e) (endV e) hu hv
    (fun k => Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                then (1 : ℝ) else 0))
    (fun k => Lindeberg.mean μ
      (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                then (1 : ℝ) else 0))
    hcompu hcompv

























theorem acl_fk_q2_hcov_of_translationComparison
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {edge : Sym2 W → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : Sym2 W → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List (Sym2 W)) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n)
    (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (conn : Site d → ℕ → ℝ) (hconnnn : ∀ x j, 0 ≤ conn x j)
    (hLu : ∀ e : Sym2 W, endU e ∈ Λ) (hLv : ∀ e : Sym2 W, endV e ∈ Λ)
    (rdist : Sym2 W → ℕ × ℕ)
    (hru : ∀ e : Sym2 W, (rdist e).1 ≤ n) (hrv : ∀ e : Sym2 W, (rdist e).2 ≤ n)
    (hcomp : ∀ (e : Sym2 W),
      (∀ k, Lindeberg.mean (fkMass G p 2)
          (fun ω => if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
          ≤ conn (endU e) ((k : ℤ) - ((rdist e).1 : ℤ)).natAbs)
      ∧ (∀ k, Lindeberg.mean (fkMass G p 2)
          (fun ω => if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k)
                    then (1 : ℝ) else 0)
          ≤ conn (endV e) ((k : ℤ) - ((rdist e).2 : ℤ)).natAbs))
    (hmaxpos : 0 < Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j)) :
    Lindeberg.mean (fkMass G p 2) (crossInd edge o n)
        * (1 - Lindeberg.mean (fkMass G p 2) (crossInd edge o n))
        / (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j) / (n : ℝ))
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
  classical
  set M := Λ.sup' hne (fun x => ∑ j ∈ Finset.range (n + 1), conn x j) with hMdef
  have hncard : (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) = (n : ℝ) := by
    rw [Fintype.card_coe, Nat.card_Icc]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  set D : ℝ := 4 * M / (n : ℝ) with hDdef
  have hDpos : 0 < D := by
    rw [hDdef]; positivity
  
  have hsum : ∀ e : Sym2 W,
      (∑ k : ↥(Finset.Icc 1 n), boxReveal (fkMass G p 2) edge endU endV (k : ℕ) e)
        ≤ (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D := by
    intro e
    have hsl := acl_boxReveal_sum_le (μ := fkMass G p 2) (edge := edge)
      (endU := endU) (endV := endV) n Λ hne conn hconnnn e (rdist e).1 (rdist e).2
      (hru e) (hrv e) (hLu e) (hLv e) (hcomp e).1 (hcomp e).2
    
    have hcardD : (Fintype.card (↥(Finset.Icc 1 n)) : ℝ) * D = 4 * M := by
      rw [hncard, hDdef]; field_simp
    rw [hcardD]; exact hsl
  
  have hmain := acl_fk_q2_hcov_crossTree G hp hp1 hinj hcoh hadj o l hl disc₀
    hdisc₀sub hdisc₀sup hoB ho n hn D hDpos hsum
  rw [hDdef] at hmain
  exact hmain














theorem acl_fk_q2_poincare_adaptive
    (G : SimpleGraph W) [DecidableRel G.Adj] {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {edge : Sym2 W → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : Sym2 W → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List (Sym2 W)) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) :
    Lindeberg.var (fkMass G p 2) (crossInd edge o n)
      ≤ ∑ e, Lindeberg.cov (fkMass G p 2) (crossInd edge o n) (Lindeberg.coord e) := by
  classical
  haveI hne : Nonempty (↥(Finset.Icc 1 n)) :=
    ⟨⟨1, by rw [Finset.mem_Icc]; exact ⟨le_refl 1, hn⟩⟩⟩
  set f : ConfigSpace (Sym2 W) → ℝ := crossInd edge o n with hf0
  set Tf : ↥(Finset.Icc 1 n) → DecisionTree (Sym2 W) :=
    fun k => crossTree endU endV o (vertexBoundary d n) l (disc₀ (k : ℕ)) with hTfdef
  have hf : Monotone f := by
    rw [hf0, crossInd]
    exact (connectedToSet_increasing edge o (vertexBoundary d n)).indicator_monotone
  have hTf : ∀ k, (Tf k).evalR = f := by
    intro k
    funext ω
    have hk1 : 1 ≤ (k : ℕ) := (Finset.mem_Icc.mp k.2).1
    have hkn : (k : ℕ) ≤ n := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree_connected (E := Sym2 W) (d := d) hinj hcoh hadj
      (k : ℕ) n hk1 hkn o (ho (k : ℕ) hk1) l hl (disc₀ (k : ℕ))
      (hdisc₀sup (k : ℕ)) (hoB (k : ℕ)) ω
    rw [hTfdef, heval, hf0, crossInd]
    by_cases hconn : ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n)
    · have hmem : ω ∈ crossEvent edge o (vertexBoundary d n) := hconn
      rw [if_pos hconn, Set.indicator_of_mem hmem]
    · have hmem : ω ∉ crossEvent edge o (vertexBoundary d n) := hconn
      rw [if_neg hconn, Set.indicator_of_notMem hmem]
  have hpos : ∀ ω, 0 < fkMass G p 2 ω :=
    fun ω => fkMass_pos G hp hp1 (by norm_num) ω
  have hμ1 : ∑ ω, fkMass G p 2 ω = 1 :=
    fkMass_sum_eq_one G hp hp1 (by norm_num)
  have hFKG : FKGLatticeCondition (fkMass G p 2) :=
    FK.fkProb_FKGLatticeCondition G hp hp1 (by norm_num)
  have h := var_le_avg_adaptive_reveal_mul_sum_cov_unconditional hpos hμ1 hFKG Tf hf hTf 1
    (fun e => frf_avg_treeReveal_le_one (fun ω => (hpos ω).le) hμ1 Tf e)
  simpa using h














theorem acl_fixedFamily_route_false {κ : Type*} (σf : κ → (Fin 3 ≃ Fin 3))
    (k₀ : κ) (hk₀ : ((σf k₀).symm 0 : ℕ) = 0) :
    ¬ PerScaleRevealmentClose.psr_FamilyFrontierConn σf
        (ReachDomination.indicatorConn PerScaleRevealmentClose.psr_witnessEndU
          PerScaleRevealmentClose.psr_witnessEndV ({0} : Set (Fin 4)) ({3} : Set (Fin 4)))
        PerScaleRevealmentClose.psr_witnessEndU PerScaleRevealmentClose.psr_witnessEndV
        (fun _ => ({0} : Set (Fin 4))) :=
  frf_familyFrontierConn_false_concrete σf k₀ hk₀

end AdaptiveCovLowerClose

end OSSS

end StatMech
