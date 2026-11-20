/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.ActiveEdges
import Code.OSSS.AdaptiveCovLowerGeom
import Code.OSSS.RussoPrefactor

open scoped BigOperators Classical
open Finset Set

namespace StatMech
namespace OSSS
namespace ActiveEdgeDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open RevealmentTranslation
open LindebergTree

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {d : ℕ}

lemma mean_active_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ) (f : ConfigSpace G.edgeSet → ℝ) :
    Lindeberg.mean (FK.activeProb G pf q) f = FK.activeMean G pf q f := by
  unfold Lindeberg.mean FK.activeMean
  apply Finset.sum_congr rfl
  intro ω _
  ring

lemma cov_active_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (pf : Sym2 V → ℝ) (q : ℝ) (f g : ConfigSpace G.edgeSet → ℝ) :
    Lindeberg.cov (FK.activeProb G pf q) f g = FK.activeCov G pf q f g := by
  unfold Lindeberg.cov FK.activeCov
  rw [mean_active_eq, mean_active_eq, mean_active_eq]


noncomputable def incidentEdges {E : Type*} [Fintype E]
    (endU endV : E → Site d) (o : Site d) : Finset E :=
  Finset.univ.filter (fun e => endU e = o ∨ endV e = o)

lemma reachOpen_first_incident {E X : Type*}
    {endU endV : E → X} {ω : ConfigSpace E} {x z : X}
    (h : ReachOpen endU endV ω x z) (hne : x ≠ z) :
    ∃ e, ω e = true ∧ (endU e = x ∨ endV e = x) := by
  cases h with
  | refl => exact absurd rfl hne
  | step e hopen hpair hrest =>
      refine ⟨e, hopen, ?_⟩
      rcases hpair with hpair | hpair
      · exact Or.inl hpair.1
      · exact Or.inr hpair.2

lemma closedProd_incident_le_cross_complement
    {E : Type*} [Fintype E] [DecidableEq E]
    {edge : E → Sym2 (Site d)} {endU endV : E → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (o : Site d) (B : Set (Site d)) (hoB : o ∉ B)
    (ω : ConfigSpace E) :
    FK.closedProd (incidentEdges endU endV o) ω ≤
      1 - (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) ω := by
  by_cases hc : ConnectedToSet d (liftCfg edge ω) o B
  · have hm : ω ∈ crossEvent edge o B := hc
    rw [Set.indicator_of_mem hm, sub_self]
    have hconn := TreeComplete.connectedToSet_imp_connOpenSet hcoh hc
    obtain ⟨b, hbB, hr⟩ := hconn
    have hbo : b ≠ o := fun h => hoB (h ▸ hbB)
    obtain ⟨e, hopen, heo⟩ := reachOpen_first_incident hr hbo.symm
    have heI : e ∈ incidentEdges endU endV o := by
      unfold incidentEdges
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, heo⟩
    unfold FK.closedProd
    rw [Finset.prod_eq_zero heI]
    simp [hopen]
  · have hm : ω ∉ crossEvent edge o B := hc
    rw [Set.indicator_of_notMem hm, sub_zero]
    unfold FK.closedProd
    exact Finset.prod_le_one (fun e he => by positivity) (fun e he => by split <;> norm_num)



theorem active_cross_one_sub_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 < J e)
    (q β β₀ : ℝ) (hq : 1 ≤ q) (hβ : 0 < β) (hββ₀ : β ≤ β₀)
    {edge : G.edgeSet → Sym2 (Site d)} {endU endV : G.edgeSet → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (o : Site d) (B : Set (Site d)) (hoB : o ∉ B) :
    (∏ e ∈ incidentEdges endU endV o, Real.exp (-(β₀ * J e.1))) ≤
      1 - Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q)
        ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))) := by
  let I := incidentEdges endU endV o
  let μ := FK.activeProb G (FK.betaParams J β) q
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hμ0 : ∀ ω, 0 ≤ μ ω := fun ω =>
    (FK.activeProb_pos G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq0 ω).le
  have hμ1 : ∑ ω, μ ω = 1 :=
    FK.activeProb_sum_eq_one G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq0
  have hparam : (∏ e ∈ I, Real.exp (-(β₀ * J e.1))) ≤
      ∏ e ∈ I, (1 - FK.betaParams J β e.1) := by
    apply Finset.prod_le_prod
    · intro e he
      exact (Real.exp_pos _).le
    · intro e he
      rw [FK.betaParams]
      simp only [sub_sub_cancel]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hββ₀ (hJ e.1).le
      linarith
  have hclosed := FK.active_prod_closed_param_le G
    (FK.betaParams_pos hJ hβ) (FK.betaParams_lt_one J β) hq I
  have hpoint : ∀ ω, μ ω * FK.closedProd I ω ≤
      μ ω * (1 - (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) ω) := by
    intro ω
    exact mul_le_mul_of_nonneg_left
      (closedProd_incident_le_cross_complement hcoh o B hoB ω) (hμ0 ω)
  calc
    (∏ e ∈ I, Real.exp (-(β₀ * J e.1)))
        ≤ ∏ e ∈ I, (1 - FK.betaParams J β e.1) := hparam
    _ ≤ ∑ ω, μ ω * FK.closedProd I ω := hclosed
    _ ≤ ∑ ω, μ ω *
        (1 - (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) ω) :=
      Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = 1 - Lindeberg.mean μ
        ((crossEvent edge o B).indicator (fun _ => (1 : ℝ))) := by
      unfold Lindeberg.mean
      rw [show (fun ω => μ ω *
          (1 - (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) ω)) =
          (fun ω => μ ω - μ ω *
            (crossEvent edge o B).indicator (fun _ => (1 : ℝ)) ω) by
        funext ω
        ring]
      rw [Finset.sum_sub_distrib, hμ1]
      congr 1
      apply Finset.sum_congr rfl
      intro ω _
      ring



theorem active_fk_differential_logistic
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 < J e)
    (q β : ℝ) (hq : 1 ≤ q) (hβ : 0 < β)
    {edge : G.edgeSet → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : G.edgeSet → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List G.edgeSet) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (hLu : ∀ e : G.edgeSet, endU e ∈ Λ)
    (hLv : ∀ e : G.edgeSet, endV e ∈ Λ)
    (hUbox : ∀ e : G.edgeSet, endU e ∈ box d n)
    (hVbox : ∀ e : G.edgeSet, endV e ∈ box d n) :
    ∃ cR : ℝ, 0 < cR ∧
      cR * (Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q)
          (crossIndG edge o n) *
        (1 - Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q)
          (crossIndG edge o n)) /
        (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (fun ω =>
            if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
            then (1 : ℝ) else 0)) / (n : ℝ))) ≤
      deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) β := by
  let μ := FK.activeProb G (FK.betaParams J β) q
  let f := crossIndG edge o n
  let D := 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
    Lindeberg.mean μ (fun ω =>
      if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
      then (1 : ℝ) else 0)) / (n : ℝ)
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hpos : ∀ ω, 0 < μ ω := by
    intro ω
    exact FK.activeProb_pos G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq0 ω
  have hμ1 : ∑ ω, μ ω = 1 :=
    FK.activeProb_sum_eq_one G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq0
  have hFKG : FKGLatticeCondition μ :=
    FK.activeProb_FKGLatticeCondition G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq
  have hcov := hcov_lattice_mass μ hpos hμ1 hFKG hinj hcoh hadj o l hl disc₀
    hdisc₀sub hdisc₀sup hoB ho n hn Λ hne hLu hLv hUbox hVbox
  have hf : Monotone f :=
    (connectedToSet_increasing edge o (vertexBoundary d n)).indicator_monotone
  have hcov0 : ∀ e : G.edgeSet,
      0 ≤ FK.activeCov G (FK.betaParams J β) q f (Lindeberg.coord e) := by
    intro e
    rw [← cov_active_eq]
    exact cov_coord_nonneg hpos hμ1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeProbOf_beta_sum G hJ hβ hq0
    (crossEvent edge o (vertexBoundary d n))
  have hderivEq : deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q
      (crossEvent edge o (vertexBoundary d n))) β =
      ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(β * J e.1)))) *
        FK.activeCov G (FK.betaParams J β) q f (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    rfl
  obtain ⟨cR, hcR, hRusso⟩ := RussoPrefactor.rp_differential_lower_weighted_beta
    (fun e : G.edgeSet => J e.1)
    (fun e => FK.activeCov G (FK.betaParams J β) q f (Lindeberg.coord e)) β
    (deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q
      (crossEvent edge o (vertexBoundary d n))) β)
    (fun e => hJ e.1) hβ hcov0 hderivEq
  refine ⟨cR, hcR, ?_⟩
  have hscaled := mul_le_mul_of_nonneg_left hcov hcR.le
  exact hscaled.trans hRusso

lemma geometricDenom_pos
    {E : Type*} [Fintype E] [DecidableEq E]
    (μ : ConfigSpace E → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ1 : ∑ ω, μ ω = 1)
    (edge : E → Sym2 (Site d)) (n : ℕ) (hn : 1 ≤ n)
    (Λ : Finset (Site d)) (hne : Λ.Nonempty) :
    0 < 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
      Lindeberg.mean μ (fun ω =>
        if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
        then (1 : ℝ) else 0)) / (n : ℝ) := by
  let conn : Site d → ℕ → ℝ := fun x j => Lindeberg.mean μ (fun ω =>
    if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
    then (1 : ℝ) else 0)
  have hne' := hne
  obtain ⟨x, hx⟩ := hne'
  have hconn0 : ∀ y j, 0 ≤ conn y j := fun y j =>
    RevealmentTranslation.mean_indicator_nonneg hμ0 _
  have hzero : conn x 0 = 1 := by
    have hall : (fun ω : ConfigSpace E =>
        if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x 0)
        then (1 : ℝ) else 0) = fun _ => 1 := by
      funext ω
      rw [if_pos]
      exact ⟨x, centeredRadius_self x, connected_refl _ _⟩
    unfold conn
    rw [hall]
    exact Lindeberg.mean_const μ hμ1 1
  have hs : 1 ≤ ∑ j ∈ Finset.range n, conn x j := by
    rw [← hzero]
    apply Finset.single_le_sum (fun j _ => hconn0 x j)
    simp
    omega
  have hsup := Finset.le_sup' (fun y => ∑ j ∈ Finset.range n, conn y j) hx
  have hM : 0 < Λ.sup' hne (fun y => ∑ j ∈ Finset.range n, conn y j) := by
    linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  change 0 < 4 * Λ.sup' hne (fun y => ∑ j ∈ Finset.range n, conn y j) / (n : ℝ)
  positivity

lemma absorb_cross_complement {θ D κ cR θ' : ℝ}
    (hθ : 0 ≤ θ) (hD : 0 < D) (hκ : 0 < κ) (hcR : 0 < cR)
    (hgap : κ ≤ 1 - θ)
    (hlog : cR * (θ * (1 - θ) / D) ≤ θ') :
    0 < cR * κ ∧ (cR * κ) * (θ / D) ≤ θ' := by
  refine ⟨mul_pos hcR hκ, ?_⟩
  have hscale : κ * (θ / D) ≤ (1 - θ) * (θ / D) :=
    mul_le_mul_of_nonneg_right hgap (div_nonneg hθ hD.le)
  calc
    (cR * κ) * (θ / D) = cR * (κ * (θ / D)) := by ring
    _ ≤ cR * ((1 - θ) * (θ / D)) := mul_le_mul_of_nonneg_left hscale hcR.le
    _ = cR * (θ * (1 - θ) / D) := by ring
    _ ≤ θ' := hlog



theorem active_fk_differential_inequality
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (J : Sym2 V → ℝ) (hJ : ∀ e, 0 < J e)
    (q β β₀ : ℝ) (hq : 1 ≤ q) (hβ : 0 < β) (hββ₀ : β ≤ β₀)
    {edge : G.edgeSet → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : G.edgeSet → Site d}
    (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List G.edgeSet) (hl : ∀ e, e ∈ l)
    (disc₀ : ℕ → Finset (Site d))
    (hdisc₀sub : ∀ k, ∀ x ∈ disc₀ k, x ∈ vertexBoundary d k)
    (hdisc₀sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc₀ k)
    (hoB : ∀ k, o ∉ disc₀ k)
    (ho : ∀ k : ℕ, 1 ≤ k → o ∈ box d (k - 1))
    (n : ℕ) (hn : 1 ≤ n) (Λ : Finset (Site d)) (hne : Λ.Nonempty)
    (hLu : ∀ e : G.edgeSet, endU e ∈ Λ)
    (hLv : ∀ e : G.edgeSet, endV e ∈ Λ)
    (hUbox : ∀ e : G.edgeSet, endU e ∈ box d n)
    (hVbox : ∀ e : G.edgeSet, endV e ∈ box d n) :
    ∃ c : ℝ, 0 < c ∧
      c * (Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q)
          (crossIndG edge o n) /
        (4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean (FK.activeProb G (FK.betaParams J β) q) (fun ω =>
            if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
            then (1 : ℝ) else 0)) / (n : ℝ))) ≤
      deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) β := by
  let μ := FK.activeProb G (FK.betaParams J β) q
  let θ := Lindeberg.mean μ (crossIndG edge o n)
  let D := 4 * Λ.sup' hne (fun x => ∑ j ∈ Finset.range n,
    Lindeberg.mean μ (fun ω =>
      if ConnectedToSet d (liftCfg edge ω) x (centeredBoundary x j)
      then (1 : ℝ) else 0)) / (n : ℝ)
  let κ := ∏ e ∈ incidentEdges endU endV o, Real.exp (-(β₀ * J e.1))
  obtain ⟨cR, hcR, hlog⟩ := active_fk_differential_logistic G J hJ q β hq hβ
    hinj hcoh hadj o l hl disc₀ hdisc₀sub hdisc₀sup hoB ho n hn Λ hne
    hLu hLv hUbox hVbox
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hμ0 : ∀ ω, 0 ≤ μ ω := fun ω =>
    (FK.activeProb_pos G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq0 ω).le
  have hμ1 : ∑ ω, μ ω = 1 :=
    FK.activeProb_sum_eq_one G (FK.betaParams_pos hJ hβ)
      (FK.betaParams_lt_one J β) hq0
  have hθ : 0 ≤ θ := by
    unfold θ Lindeberg.mean
    apply Finset.sum_nonneg
    intro ω _
    exact mul_nonneg (by
      unfold crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num) (hμ0 ω)
  have hD : 0 < D := geometricDenom_pos μ hμ0 hμ1 edge n hn Λ hne
  have hκ : 0 < κ := by
    unfold κ
    exact Finset.prod_pos (fun e he => Real.exp_pos _)
  have hoBoundary : o ∉ vertexBoundary d n := fun h => hoB n (hdisc₀sup n o h)
  have hgap : κ ≤ 1 - θ := by
    simpa [κ, θ, μ, crossIndG] using
      active_cross_one_sub_lower G J hJ q β β₀ hq hβ hββ₀ hcoh o
        (vertexBoundary d n) hoBoundary
  have hlog' : cR * (θ * (1 - θ) / D) ≤
      deriv (fun b => FK.activeProbOf G (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) β := by
    simpa [θ, D, μ] using hlog
  obtain ⟨hc, hmain⟩ := absorb_cross_complement hθ hD hκ hcR hgap hlog'
  exact ⟨cR * κ, hc, by simpa [θ, D, μ] using hmain⟩

end ActiveEdgeDifferential
end OSSS
end StatMech
