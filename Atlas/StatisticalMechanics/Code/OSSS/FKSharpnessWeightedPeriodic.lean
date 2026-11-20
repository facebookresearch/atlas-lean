/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.OSSS.FKSharpnessWeighted
import Code.OSSS.WiredBoxLocalized
import Code.OSSS.WiredBoxOffCentre

open scoped BigOperators Classical
open Finset Set Filter Topology

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedPeriodic

open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open WiredBoxDifferential FK RevealmentTranslation
open FKSharpnessWeighted
open ActiveBoundaryDifferential ActiveEdgeDifferential LindebergTree


def translateAmbientEdge {d : Nat} (x : Site d) (e : Sym2 (Site d)) :
    Sym2 (Site d) :=
  Sym2.map (fun y => y + x) e




def PhaseCovariant {d : Nat} {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real) : Prop :=
  forall x e, J (translateAmbientEdge x e) = phaseJ (phase x) e


def boxCoupling {d : Nat} (J : Sym2 (Site d) -> Real) (R : Nat) :
    Sym2 (boxVerts d R) -> Real :=
  fun e => J (Sym2.map Subtype.val e)


def transBoxCoupling {d : Nat} (J : Sym2 (Site d) -> Real)
    (R : Nat) (x : Site d) : Sym2 (fvs_transBoxVerts d R x) -> Real :=
  fun e => J (Sym2.map Subtype.val e)


def phaseBoxCoupling {d : Nat} {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P) (R : Nat) :
    Sym2 (boxVerts d R) -> Real :=
  boxCoupling (phaseJ a) R



theorem transBoxCoupling_map_eq_phaseBoxCoupling
    {d : Nat} {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (R : Nat) (x : Site d) (e : Sym2 (boxVerts d R)) :
    transBoxCoupling J R x (Sym2.map (fvs_transEquiv d R x) e) =
      phaseBoxCoupling phaseJ (phase x) R e := by
  unfold transBoxCoupling phaseBoxCoupling boxCoupling
  rw [Sym2.map_map]
  have hfun :
      (Subtype.val ∘ (fvs_transEquiv d R x : boxVerts d R ->
        fvs_transBoxVerts d R x)) = (fun y : boxVerts d R => (y : Site d) + x) := by
    funext y
    rfl
  rw [hfun]
  calc
    J (Sym2.map (fun y : boxVerts d R => (y : Site d) + x) e) =
        J (translateAmbientEdge x (Sym2.map Subtype.val e)) := by
      congr 1
      unfold translateAmbientEdge
      rw [Sym2.map_map]
      rfl
    _ = phaseJ (phase x) (Sym2.map Subtype.val e) :=
      hcov x (Sym2.map Subtype.val e)

theorem PhaseCovariant.eq_of_same_phase
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    {x y : Site d} (hxy : phase x = phase y) (e : Sym2 (Site d)) :
    J (translateAmbientEdge x e) = J (translateAmbientEdge y e) := by
  rw [hcov x e, hcov y e, hxy]

theorem PhaseCovariant.phaseCoupling_pos
    {d : Nat} {P : Type*}
    {J : Sym2 (Site d) -> Real} {phase : Site d -> P}
    {phaseJ : P -> Sym2 (Site d) -> Real}
    (hcov : PhaseCovariant J phase phaseJ)
    (hsurj : Function.Surjective phase) (hJ : forall e, 0 < J e) :
    forall a e, 0 < phaseJ a e := by
  intro a e
  obtain ⟨x, rfl⟩ := hsurj a
  rw [← hcov x e]
  exact hJ _


theorem betaParams_transBox_map_eq_phaseBox
    {d : Nat} {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hcov : PhaseCovariant J phase phaseJ)
    (R : Nat) (x : Site d) (beta : Real) (e : Sym2 (boxVerts d R)) :
    FK.betaParams (transBoxCoupling J R x) beta
        (Sym2.map (fvs_transEquiv d R x) e) =
      FK.betaParams (phaseBoxCoupling phaseJ (phase x) R) beta e := by
  unfold FK.betaParams
  rw [transBoxCoupling_map_eq_phaseBoxCoupling J phase phaseJ hcov R x e]


noncomputable def phaseEnvelope {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (n : Nat) : Real :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => theta a n)




noncomputable def weightedPhaseWiredTheta
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real) (a : P)
    (q beta : Real) (k : Nat) : Real :=
  Lindeberg.mean
    (FK.activeBCProb (boxGraph d (2 * k))
      (wiredBoxBoundaryGraph d (2 * k))
      (FK.betaParams (phaseBoxCoupling phaseJ a (2 * k)) beta) q)
    (WiredBoxLocalized.innerCrossInd d k)

theorem weightedPhaseWiredTheta_nonneg
    (d : Nat) {P : Type*}
    (phaseJ : P -> Sym2 (Site d) -> Real)
    (hJ : forall a e, 0 < phaseJ a e)
    (a : P) (q beta : Real) (hq : 0 < q) (hbeta : 0 < beta)
    (k : Nat) :
    0 <= weightedPhaseWiredTheta d phaseJ a q beta k := by
  unfold weightedPhaseWiredTheta Lindeberg.mean
  apply Finset.sum_nonneg
  intro omega homega
  apply mul_nonneg
  · unfold WiredBoxLocalized.innerCrossInd crossIndG
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (FK.activeBCProb_pos _ _
      (FK.betaParams_pos (fun e => hJ a (Sym2.map Subtype.val e)) hbeta)
      (FK.betaParams_lt_one _ beta) hq omega).le

theorem le_phaseEnvelope {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (a : P) (n : Nat) :
    theta a n <= phaseEnvelope theta n := by
  exact Finset.le_sup' (fun b => theta b n) (Finset.mem_univ a)

theorem phaseEnvelope_nonneg {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (htheta : forall a n, 0 <= theta a n)
    (n : Nat) : 0 <= phaseEnvelope theta n := by
  obtain ⟨a⟩ := (inferInstance : Nonempty P)
  exact (htheta a n).trans (le_phaseEnvelope theta a n)




def WeightedPhaseOffCentre (d n : Nat) {P : Type*}
    (J : Sym2 (boxVerts d n) -> Real) (phase : Site d -> P)
    (theta : P -> Nat -> Real) (q beta : Real) : Prop :=
  forall x, x ∈ osssBoxFinset d n -> forall k, k ∈ Finset.range n ->
    Lindeberg.mean
        (FK.activeBCProb (boxGraph d n) (wiredBoxBoundaryGraph d n)
          (FK.betaParams J beta) q)
        (fun omega => if ConnectedToSet d
          (liftCfg (boxActiveEdge d n) omega) x (centeredBoundary x k)
          then (1 : Real) else 0) <=
      theta (phase x) k




def PeriodicWeightedNestedDomination
    (d n : Nat) {P : Type*}
    (J : Sym2 (Site d) -> Real) (phase : Site d -> P)
    (phaseJ : P -> Sym2 (Site d) -> Real) (q beta : Real) : Prop :=
  PhaseCovariant J phase phaseJ ∧
    WeightedPhaseOffCentre d n (boxCoupling J n) phase
      (fun a => weightedPhaseWiredTheta d phaseJ a q beta) q beta


noncomputable def weightedPhaseDenom {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (n : Nat) : Real :=
  4 * (∑ k ∈ Finset.range n, phaseEnvelope theta k) / (n : Real)



theorem weightedWiredActiveDenom_le_phaseDenom
    (d n : Nat) {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (boxVerts d n) -> Real) (phase : Site d -> P)
    (theta : P -> Nat -> Real) (q beta : Real)
    (hoff : WeightedPhaseOffCentre d n J phase theta q beta) :
    weightedWiredActiveDenom d n J q beta <= weightedPhaseDenom theta n := by
  unfold weightedWiredActiveDenom weightedPhaseDenom
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sup'_le ⟨0, origin_mem_osssBoxFinset d n⟩
  intro x hx
  apply Finset.sum_le_sum
  intro k hk
  exact (hoff x hx k hk).trans (le_phaseEnvelope theta (phase x) k)




theorem weightedPhaseDenom_pos_of_pos
    {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (htheta : forall a k, 0 <= theta a k)
    (n k : Nat) (hk : k ∈ Finset.range n)
    (a : P) (hpos : 0 < theta a k) :
    0 < weightedPhaseDenom theta n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro hn0
    subst n
    simp at hk)
  have henv : 0 < phaseEnvelope theta k :=
    hpos.trans_le (le_phaseEnvelope theta a k)
  have hsum : 0 < ∑ j ∈ Finset.range n, phaseEnvelope theta j := by
    exact Finset.sum_pos' (fun j hj => phaseEnvelope_nonneg theta htheta j)
      ⟨k, hk, henv⟩
  unfold weightedPhaseDenom
  positivity



theorem weighted_wired_box_phase_differential_inequality
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (boxVerts d n) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (theta : P -> Nat -> Real)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0)
    (hoff : WeightedPhaseOffCentre d n J phase theta q beta) :
    exists c : Real, 0 < c ∧
      c * (weightedWiredActiveTheta d n J q beta /
        weightedPhaseDenom theta n) <=
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  obtain ⟨c, hc, hdiff⟩ := weighted_wired_box_differential_inequality
    d n hd hn J hJ q beta beta0 hq hbeta hbeta0
  have hden0 := weightedWiredActiveDenom_pos d n hn J hJ q beta hq hbeta
  have hdenle := weightedWiredActiveDenom_le_phaseDenom
    d n J phase theta q beta hoff
  have htheta0 : 0 <= weightedWiredActiveTheta d n J q beta := by
    unfold weightedWiredActiveTheta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega homega
    apply mul_nonneg
    · unfold crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJ hbeta)
        (FK.betaParams_lt_one J beta) (zero_lt_one.trans_le hq) omega).le
  have hratio :
      weightedWiredActiveTheta d n J q beta / weightedPhaseDenom theta n <=
        weightedWiredActiveTheta d n J q beta /
          weightedWiredActiveDenom d n J q beta :=
    div_le_div_of_nonneg_left htheta0 hden0 hdenle
  refine ⟨c, hc, ?_⟩
  exact (mul_le_mul_of_nonneg_left hratio hc.le).trans hdiff



theorem weighted_wired_box_differential_uniform_bounds
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    (J : Sym2 (boxVerts d n) -> Real)
    (Jmin Jmax q beta beta0 : Real)
    (hJmin : 0 < Jmin) (hJlo : forall e, Jmin <= J e)
    (hJhi : forall e, J e <= Jmax)
    (hq : 1 <= q) (hbeta : 0 < beta) (hbeta0 : beta <= beta0) :
    Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) *
        (weightedWiredActiveTheta d n J q beta /
          weightedWiredActiveDenom d n J q beta) <=
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams J b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  classical
  letI : Nonempty (boxGraph d n).edgeSet :=
    boxGraph_edgeSet_nonempty d n hd hn
  let G := boxGraph d n
  let C := wiredBoxBoundaryGraph d n
  let edge := boxActiveEdge d n
  let endU := boxActiveEndU d n
  let endV := boxActiveEndV d n
  let Lambda := osssBoxFinset d n
  let disc0 : Nat -> Finset (Site d) := osssBoundaryFinset d
  let mu := FK.activeBCProb G C (FK.betaParams J beta) q
  let f := crossIndG edge 0 n
  let D := weightedWiredActiveDenom d n J q beta
  let theta := weightedWiredActiveTheta d n J q beta
  let I := incidentEdges endU endV (0 : Site d)
  let kappa := Real.exp (-(beta0 * Jmax)) ^ (2 * d)
  have hJ : forall e, 0 < J e := fun e => hJmin.trans_le (hJlo e)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpos : forall omega, 0 < mu omega := fun omega =>
    FK.activeBCProb_pos G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0 omega
  have hmu1 : ∑ omega, mu omega = 1 :=
    FK.activeBCProb_sum_eq_one G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    FK.activeBCProb_FKGLatticeCondition G C (FK.betaParams_pos hJ hbeta)
      (FK.betaParams_lt_one J beta) hq
  have hl : forall e : G.edgeSet,
      e ∈ (Finset.univ : Finset G.edgeSet).toList := by simp
  have hdisc0sub : forall k x, x ∈ disc0 k -> x ∈ vertexBoundary d k := by
    intro k x hx
    simpa [disc0] using hx
  have hdisc0sup : forall k x, x ∈ vertexBoundary d k -> x ∈ disc0 k := by
    intro k x hx
    simpa [disc0] using hx
  have hoB : forall k, (0 : Site d) ∉ disc0 k := by
    intro k
    exact origin_not_mem_osssBoundaryFinset d k
  have ho : forall k : Nat, 1 <= k -> (0 : Site d) ∈ box d (k - 1) := by
    intro k hk i
    simp
  have hcov := hcov_lattice_mass mu hpos hmu1 hFKG
    (boxActiveEdge_injective d n) (boxActiveEdge_eq_endpoints d n)
    (boxActiveEnd_adj d n) (0 : Site d)
    (Finset.univ : Finset G.edgeSet).toList hl disc0 hdisc0sub hdisc0sup
    hoB ho n hn Lambda ⟨0, origin_mem_osssBoxFinset d n⟩
    (boxActiveEndU_mem d n) (boxActiveEndV_mem d n)
    (fun e => e.1.out.1.property) (fun e => e.1.out.2.property)
  have hf : Monotone f :=
    (connectedToSet_increasing edge 0 (vertexBoundary d n)).indicator_monotone
  have hcov0 : forall e : G.edgeSet,
      0 <= FK.activeBCCov G C (FK.betaParams J beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← cov_activeBC_eq]
    exact cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := FK.hasDerivAt_activeBCProbOf_beta_sum G C hJ hbeta hq0
    (crossEvent edge 0 (vertexBoundary d n))
  have hderivEq :
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge 0 (vertexBoundary d n))) beta =
      ∑ e : G.edgeSet, (J e.1 / (1 - Real.exp (-(beta * J e.1)))) *
        FK.activeBCCov G C (FK.betaParams J beta) q f
          (Lindeberg.coord e) := by
    simpa [f, crossIndG] using hderiv.deriv
  have hpref : forall e : G.edgeSet,
      Jmin <= J e.1 / (1 - Real.exp (-(beta * J e.1))) := by
    intro e
    have hden0 : 0 < 1 - Real.exp (-(beta * J e.1)) := by
      have := Real.exp_lt_one_iff.mpr
        (neg_lt_zero.mpr (mul_pos hbeta (hJ e.1)))
      linarith
    rw [le_div_iff₀ hden0]
    have hden1 : 1 - Real.exp (-(beta * J e.1)) <= 1 := by
      linarith [Real.exp_pos (-(beta * J e.1))]
    calc
      Jmin * (1 - Real.exp (-(beta * J e.1))) <= Jmin * 1 :=
        mul_le_mul_of_nonneg_left hden1 hJmin.le
      _ = Jmin := mul_one Jmin
      _ <= J e.1 := hJlo e.1
  have hRusso : Jmin * ∑ e : G.edgeSet,
      FK.activeBCCov G C (FK.betaParams J beta) q f (Lindeberg.coord e) <=
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge 0 (vertexBoundary d n))) beta := by
    rw [hderivEq]
    exact RussoPrefactor.rp_prefactor_extraction _ _ Jmin hpref hcov0
  have hlog : Jmin * (theta * (1 - theta) / D) <=
      deriv (fun b => FK.activeBCProbOf G C (FK.betaParams J b) q
        (crossEvent edge 0 (vertexBoundary d n))) beta := by
    have hs := mul_le_mul_of_nonneg_left hcov hJmin.le
    apply hs.trans
    simpa [G, C, edge, mu, f, theta, D, weightedWiredActiveTheta,
      weightedWiredActiveDenom, Lambda] using hRusso
  have htheta0 : 0 <= theta := by
    unfold theta weightedWiredActiveTheta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega homega
    exact mul_nonneg (by
      unfold crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num) (hpos omega).le
  have hD : 0 < D := by
    simpa [D] using weightedWiredActiveDenom_pos d n hn J hJ q beta hq hbeta
  have hbeta0pos : 0 < beta0 := hbeta.trans_le hbeta0
  let e0 : G.edgeSet := Classical.choice (inferInstance : Nonempty G.edgeSet)
  have hJmax : 0 < Jmax := (hJ e0.1).trans_le (hJhi e0.1)
  have hkbase0 : 0 < Real.exp (-(beta0 * Jmax)) := Real.exp_pos _
  have hkbase1 : Real.exp (-(beta0 * Jmax)) <= 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hbeta0pos hJmax])
  have hIcard : I.card <= 2 * d := by
    simpa [I, endU, endV] using
      WiredBoxOffCentre.wiredOuterIncident_card_le d n
  have hkpow : kappa <= Real.exp (-(beta0 * Jmax)) ^ I.card := by
    unfold kappa
    exact pow_le_pow_of_le_one hkbase0.le hkbase1 hIcard
  have hterm : forall e, e ∈ I ->
      Real.exp (-(beta0 * Jmax)) <= Real.exp (-(beta0 * J e.1)) := by
    intro e he
    apply Real.exp_le_exp.mpr
    nlinarith [hJhi e.1]
  have hkprod : kappa <= I.prod
      (fun e => Real.exp (-(beta0 * J e.1))) := by
    exact hkpow.trans (by
      simpa [Finset.prod_const] using Finset.prod_le_prod (fun e he =>
        hkbase0.le) hterm)
  have hoBoundary : (0 : Site d) ∉ vertexBoundary d n := by
    intro h
    apply origin_not_mem_osssBoundaryFinset d n
    rw [mem_osssBoundaryFinset]
    exact h
  have hgapRaw := activeBC_cross_one_sub_lower G C J hJ q beta beta0
    hq hbeta hbeta0 (boxActiveEdge_eq_endpoints d n) (0 : Site d)
    (vertexBoundary d n) hoBoundary
  have hgap : kappa <= 1 - theta := hkprod.trans (by
    simpa [G, C, edge, endU, endV, I, mu, f, theta,
      weightedWiredActiveTheta, crossIndG] using hgapRaw)
  have hkappa : 0 < kappa := by
    unfold kappa
    positivity
  obtain ⟨_, hmain⟩ := absorb_cross_complement
    htheta0 hD hkappa hJmin hgap hlog
  simpa [G, C, edge, D, theta, kappa, weightedWiredActiveTheta,
    weightedWiredActiveDenom] using hmain



theorem weighted_periodic_box_differential_inequality
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0)
    (hnested : PeriodicWeightedNestedDomination
      d n J phase phaseJ q beta) :
    exists c : Real, 0 < c ∧
      c * (weightedWiredActiveTheta d n (boxCoupling J n) q beta /
        weightedPhaseDenom
          (fun a => weightedPhaseWiredTheta d phaseJ a q beta) n) <=
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (boxCoupling J n) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  apply weighted_wired_box_phase_differential_inequality
    d n hd hn (boxCoupling J n) (fun e => hJ (Sym2.map Subtype.val e))
    phase (fun a => weightedPhaseWiredTheta d phaseJ a q beta)
    q beta beta0 hq hbeta hbeta0
  exact hnested.2



theorem weighted_periodic_box_differential_uniform_bounds
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin Jmax : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e) (hJhi : forall e, J e <= Jmax)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (q beta beta0 : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    (hbeta0 : beta <= beta0)
    (hnested : PeriodicWeightedNestedDomination
      d n J phase phaseJ q beta) :
    Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) *
        (weightedWiredActiveTheta d n (boxCoupling J n) q beta /
          weightedPhaseDenom
            (fun a => weightedPhaseWiredTheta d phaseJ a q beta) n) <=
      deriv (fun b => FK.activeBCProbOf (boxGraph d n)
        (wiredBoxBoundaryGraph d n) (FK.betaParams (boxCoupling J n) b) q
        (crossEvent (boxActiveEdge d n) 0 (vertexBoundary d n))) beta := by
  let Jbox := boxCoupling J n
  let theta := fun a => weightedPhaseWiredTheta d phaseJ a q beta
  have hJbox : forall e, 0 < Jbox e := fun e =>
    hJmin.trans_le (hJlo (Sym2.map Subtype.val e))
  have hden0 := weightedWiredActiveDenom_pos
    d n hn Jbox hJbox q beta hq hbeta
  have hdenle := weightedWiredActiveDenom_le_phaseDenom
    d n Jbox phase theta q beta hnested.2
  have htheta0 :
      0 <= weightedWiredActiveTheta d n Jbox q beta := by
    unfold weightedWiredActiveTheta Lindeberg.mean
    apply Finset.sum_nonneg
    intro omega homega
    apply mul_nonneg
    · unfold crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    · exact (FK.activeBCProb_pos _ _ (FK.betaParams_pos hJbox hbeta)
        (FK.betaParams_lt_one Jbox beta) (zero_lt_one.trans_le hq) omega).le
  have hratio :
      weightedWiredActiveTheta d n Jbox q beta /
          weightedPhaseDenom theta n <=
        weightedWiredActiveTheta d n Jbox q beta /
          weightedWiredActiveDenom d n Jbox q beta :=
    div_le_div_of_nonneg_left htheta0 hden0 hdenle
  have hconst : 0 <= Jmin * Real.exp (-(beta0 * Jmax)) ^ (2 * d) := by
    positivity
  have hbase := weighted_wired_box_differential_uniform_bounds
    d n hd hn Jbox Jmin Jmax q beta beta0 hJmin
    (fun e => hJlo (Sym2.map Subtype.val e))
    (fun e => hJhi (Sym2.map Subtype.val e)) hq hbeta hbeta0
  exact (mul_le_mul_of_nonneg_left hratio hconst).trans (by
    simpa [Jbox, theta] using hbase)


theorem tendsto_finset_sup'
    {P X : Type*} [DecidableEq P] {l : Filter X}
    (s : Finset P) (hs : s.Nonempty)
    (f : P -> X -> Real) (a : P -> Real)
    (hf : forall p, p ∈ s -> Tendsto (f p) l (nhds (a p))) :
    Tendsto (fun x => s.sup' hs (fun p => f p x)) l
      (nhds (s.sup' hs a)) := by
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert p s hp ih =>
      by_cases hs' : s.Nonempty
      · have hpT : Tendsto (f p) l (nhds (a p)) := hf p (by simp)
        have hsT : Tendsto (fun x => s.sup' hs' (fun b => f b x)) l
            (nhds (s.sup' hs' a)) :=
          ih hs' (fun b hb => hf b (by simp [hb]))
        simpa only [Finset.sup'_insert hs'] using hpT.max hsT
      · have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs'
        subst s
        simpa using hf p (by simp)




theorem phaseEnvelope_tendsto
    {P : Type*} [Fintype P] [Nonempty P]
    (theta : P -> Nat -> Real) (thetaInf : P -> Real)
    (hlim : forall a, Tendsto (theta a) atTop (nhds (thetaInf a))) :
    Tendsto (phaseEnvelope theta) atTop
      (nhds (Finset.univ.sup' Finset.univ_nonempty thetaInf)) := by
  exact tendsto_finset_sup' Finset.univ Finset.univ_nonempty
    (fun a n => theta a n) thetaInf (fun a ha => hlim a)



theorem phaseSup_pos_iff
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real) :
    0 < Finset.univ.sup' Finset.univ_nonempty thetaInf ↔
      exists a, 0 < thetaInf a := by
  constructor
  · intro h
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    have hle : Finset.univ.sup' Finset.univ_nonempty thetaInf <= 0 := by
      apply Finset.sup'_le Finset.univ_nonempty
      intro a ha
      exact hnone a
    linarith
  · rintro ⟨a, ha⟩
    exact ha.trans_le (Finset.le_sup' thetaInf (Finset.mem_univ a))



theorem phaseSup_transition_iff
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real) (betaC beta : Real)
    (hphase : forall a, 0 < thetaInf a beta ↔ betaC < beta) :
    0 < Finset.univ.sup' Finset.univ_nonempty (fun a => thetaInf a beta) ↔
      betaC < beta := by
  rw [phaseSup_pos_iff]
  constructor
  · rintro ⟨a, ha⟩
    exact (hphase a).mp ha
  · intro h
    obtain ⟨a⟩ := (inferInstance : Nonempty P)
    exact ⟨a, (hphase a).mpr h⟩



theorem phaseSup_zeroSet_eq_Iic
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real) (betaC : Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (hphase : forall a beta, 0 < thetaInf a beta ↔ betaC < beta) :
    {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun a => thetaInf a beta) = 0} = Set.Iic betaC := by
  ext beta
  constructor
  · intro hz
    change Finset.univ.sup' Finset.univ_nonempty
      (fun a => thetaInf a beta) = 0 at hz
    by_contra hnot
    change ¬ beta <= betaC at hnot
    have hlt : betaC < beta := lt_of_not_ge hnot
    have hpos := (phaseSup_transition_iff thetaInf betaC beta
      (fun a => hphase a beta)).mpr hlt
    linarith
  · intro hle
    change beta <= betaC at hle
    apply le_antisymm
    · apply le_of_not_gt
      intro hpos
      have hlt := (phaseSup_transition_iff thetaInf betaC beta
        (fun a => hphase a beta)).mp hpos
      exact (not_lt_of_ge hle) hlt
    · obtain ⟨a⟩ := (inferInstance : Nonempty P)
      exact (hnonneg a beta).trans
        (Finset.le_sup' (fun b => thetaInf b beta) (Finset.mem_univ a))



theorem phaseSup_critical_eq
    {P : Type*} [Fintype P] [Nonempty P]
    (thetaInf : P -> Real -> Real) (betaC : Real)
    (hnonneg : forall a beta, 0 <= thetaInf a beta)
    (hphase : forall a beta, 0 < thetaInf a beta ↔ betaC < beta) :
    sSup {beta | Finset.univ.sup' Finset.univ_nonempty
        (fun a => thetaInf a beta) = 0} = betaC := by
  rw [phaseSup_zeroSet_eq_Iic thetaInf betaC hnonneg hphase]
  exact csSup_Iic

end FKSharpnessWeightedPeriodic
end OSSS
end StatMech
