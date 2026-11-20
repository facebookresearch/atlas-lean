/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FK.ActiveBoundaryEdges
import Code.OSSS.ActiveEdgeDifferential

open scoped BigOperators Classical
open Finset Set

namespace StatMech
namespace OSSS
namespace ActiveBoundaryDifferential

open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open RevealmentTranslation LindebergTree
open ActiveEdgeDifferential

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {d : Nat}

lemma cov_activeBC_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (pf : Sym2 V -> Real) (q : Real)
    (f g : ConfigSpace G.edgeSet -> Real) :
    Lindeberg.cov (FK.activeBCProb G C pf q) f g =
      FK.activeBCCov G C pf q f g := by
  unfold Lindeberg.cov FK.activeBCCov Lindeberg.mean FK.activeBCMean
  rfl


theorem activeBC_cross_one_sub_lower
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (J : Sym2 V -> Real) (hJ : forall e, 0 < J e)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0)
    {edge : G.edgeSet -> Sym2 (Site d)}
    {endU endV : G.edgeSet -> Site d}
    (hcoh : forall e, edge e = s(endU e, endV e))
    (o : Site d) (B : Set (Site d)) (hoB : o ∉ B) :
    (incidentEdges endU endV o).prod
        (fun e => Real.exp (-(beta0 * J e.1))) <=
      1 - Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q)
        ((crossEvent edge o B).indicator fun _ => (1 : Real)) := by
  let I := incidentEdges endU endV o
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hparam : I.prod (fun e => Real.exp (-(beta0 * J e.1))) <=
      I.prod (fun e => 1 - FK.betaParams J beta e.1) := by
    apply Finset.prod_le_prod
    · intro e he
      exact (Real.exp_pos _).le
    · intro e he
      rw [FK.betaParams]
      simp only [sub_sub_cancel]
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_right hbeta0 (hJ e.1).le
      linarith
  have hclosed := FK.activeBC_prod_closed_param_le G C
    (FK.betaParams_pos hJ hbeta) (FK.betaParams_lt_one J beta) hq I
  have hpoint : forall omega, mu omega * FK.closedProd I omega <=
      mu omega * (1 - (crossEvent edge o B).indicator
        (fun _ => (1 : Real)) omega) := by
    intro omega
    exact mul_le_mul_of_nonneg_left
      (closedProd_incident_le_cross_complement hcoh o B hoB omega) (hmu0 omega)
  calc
    I.prod (fun e => Real.exp (-(beta0 * J e.1))) <=
        I.prod (fun e => 1 - FK.betaParams J beta e.1) := hparam
    _ <= ∑ omega, mu omega * FK.closedProd I omega := hclosed
    _ <= ∑ omega, mu omega *
        (1 - (crossEvent edge o B).indicator (fun _ => (1 : Real)) omega) :=
      Finset.sum_le_sum fun omega _ => hpoint omega
    _ = 1 - Lindeberg.mean mu
        ((crossEvent edge o B).indicator fun _ => (1 : Real)) := by
      unfold Lindeberg.mean
      rw [show (fun omega => mu omega *
          (1 - (crossEvent edge o B).indicator (fun _ => (1 : Real)) omega)) =
          (fun omega => mu omega - mu omega *
            (crossEvent edge o B).indicator (fun _ => (1 : Real)) omega) by
        funext omega
        ring]
      rw [Finset.sum_sub_distrib, hmu1]
      congr 1
      exact Finset.sum_congr rfl fun omega _ => by ring



theorem activeBC_fk_differential_logistic
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (J : Sym2 V -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    {edge : G.edgeSet -> Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : G.edgeSet -> Site d}
    (hcoh : forall e, edge e = s(endU e, endV e))
    (hadj : forall e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List G.edgeSet) (hl : forall e, e ∈ l)
    (disc0 : Nat -> Finset (Site d))
    (hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k)
    (hdisc0sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc0 k)
    (hoB : forall k, o ∉ disc0 k)
    (ho : forall k : Nat, 1 <= k -> o ∈ box d (k - 1))
    (n : Nat) (hn : 1 <= n) (Lambda : Finset (Site d))
    (hne : Lambda.Nonempty)
    (hLu : forall e : G.edgeSet, endU e ∈ Lambda)
    (hLv : forall e : G.edgeSet, endV e ∈ Lambda)
    (hUbox : forall e : G.edgeSet, endU e ∈ box d n)
    (hVbox : forall e : G.edgeSet, endV e ∈ box d n) :
    exists cR : Real, 0 < cR ∧
      cR * (Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q)
          (crossIndG edge o n) *
        (1 - Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q)
          (crossIndG edge o n)) /
        (4 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q)
            (fun omega => if ConnectedToSet d (liftCfg edge omega) x
              (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real))) <=
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) beta := by
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := crossIndG edge o n
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hpos : forall omega, 0 < mu omega := fun omega =>
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hcov := hcov_lattice_mass mu hpos hmu1 hFKG hinj hcoh hadj o l hl disc0
    hdisc0sub hdisc0sup hoB ho n hn Lambda hne hLu hLv hUbox hVbox
  have hf : Monotone f :=
    (connectedToSet_increasing edge o (vertexBoundary d n)).indicator_monotone
  have hcov0 : forall e : G.edgeSet,
      0 <= FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← cov_activeBC_eq]
    exact cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCProbOf_beta_sum G C hJ hbeta hq0
    (crossEvent edge o (vertexBoundary d n))
  have hderivEq :
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) beta =
      ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
        FK.activeBCCov G C (FK.betaParams J beta) q f (Lindeberg.coord e) := by
    rw [hderiv.deriv]
    rfl
  obtain ⟨cR, hcR, hRusso⟩ :=
    RussoPrefactor.rp_differential_lower_weighted_beta
      (fun e : G.edgeSet => J e.1)
      (fun e => FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e)) beta
      (deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) beta)
      (fun e => hJ e.1) hbeta hcov0 hderivEq
  refine ⟨cR, hcR, ?_⟩
  exact (mul_le_mul_of_nonneg_left hcov hcR.le).trans hRusso



theorem activeBC_fk_differential_inequality
    (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty G.edgeSet]
    (C : SimpleGraph V) [DecidableRel C.Adj]
    (J : Sym2 V -> Real) (hJ : forall e, 0 < J e)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0)
    {edge : G.edgeSet -> Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : G.edgeSet -> Site d}
    (hcoh : forall e, edge e = s(endU e, endV e))
    (hadj : forall e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (l : List G.edgeSet) (hl : forall e, e ∈ l)
    (disc0 : Nat -> Finset (Site d))
    (hdisc0sub : ∀ k, ∀ x ∈ disc0 k, x ∈ vertexBoundary d k)
    (hdisc0sup : ∀ k, ∀ b ∈ vertexBoundary d k, b ∈ disc0 k)
    (hoB : forall k, o ∉ disc0 k)
    (ho : forall k : Nat, 1 <= k -> o ∈ box d (k - 1))
    (n : Nat) (hn : 1 <= n) (Lambda : Finset (Site d))
    (hne : Lambda.Nonempty)
    (hLu : forall e : G.edgeSet, endU e ∈ Lambda)
    (hLv : forall e : G.edgeSet, endV e ∈ Lambda)
    (hUbox : forall e : G.edgeSet, endU e ∈ box d n)
    (hVbox : forall e : G.edgeSet, endV e ∈ box d n) :
    exists c : Real, 0 < c ∧
      c * (Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q)
          (crossIndG edge o n) /
        (4 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n,
          Lindeberg.mean (FK.activeBCProb G C (FK.betaParams J beta) q)
            (fun omega => if ConnectedToSet d (liftCfg edge omega) x
              (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real))) <=
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) beta := by
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let theta := Lindeberg.mean mu (crossIndG edge o n)
  let D := 4 * Lambda.sup' hne (fun x => ∑ j ∈ Finset.range n,
    Lindeberg.mean mu (fun omega => if ConnectedToSet d (liftCfg edge omega) x
      (centeredBoundary x j) then (1 : Real) else 0)) / (n : Real)
  let kappa := (incidentEdges endU endV o).prod
    (fun e => Real.exp (-(beta0 * J e.1)))
  obtain ⟨cR, hcR, hlog⟩ := activeBC_fk_differential_logistic G C J hJ
    q beta hq hbeta hinj hcoh hadj o l hl disc0 hdisc0sub hdisc0sup hoB ho
    n hn Lambda hne hLu hLv hUbox hVbox
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have htheta : 0 <= theta := by
    unfold theta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega _
    exact mul_nonneg (by
      unfold crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num) (hmu0 omega)
  have hD : 0 < D := geometricDenom_pos mu hmu0 hmu1 edge n hn Lambda hne
  have hkappa : 0 < kappa := by
    unfold kappa
    exact Finset.prod_pos fun e he => Real.exp_pos _
  have hoBoundary : o ∉ vertexBoundary d n := fun h => hoB n (hdisc0sup n o h)
  have hgap : kappa <= 1 - theta := by
    simpa [kappa, theta, mu, crossIndG] using
      activeBC_cross_one_sub_lower G C J hJ q beta beta0 hq hbeta hbeta0
        hcoh o (vertexBoundary d n) hoBoundary
  have hlog' : cR * (theta * (1 - theta) / D) <=
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge o (vertexBoundary d n))) beta := by
    simpa [theta, D, mu] using hlog
  obtain ⟨hc, hmain⟩ := absorb_cross_complement htheta hD hkappa hcR hgap hlog'
  exact ⟨cR * kappa, hc, by simpa [theta, D, mu] using hmain⟩

end ActiveBoundaryDifferential
end OSSS
end StatMech
