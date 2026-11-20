/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.OSSS.FKSharpnessWeightedStrict

open scoped BigOperators Classical
open Finset Set

namespace StatMech
namespace OSSS
namespace FKSharpnessWeightedLocalized

open Lattice FK RevealmentConstruction RevealmentTranslation
open AdaptiveCovLowerGeom LocalizedCrossTree DecisionTree
open WiredBoxDifferential WiredBoxLocalized
open ActiveBoundaryDifferential LindebergTree RussoPrefactor
open FKSharpnessWeightedPeriodic FKSharpnessWeightedPeriodicRepair
open FKSharpnessWeightedStrict



noncomputable def weightedLocalizedTheta
    (d n : Nat) (J : Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  Lindeberg.mean
    (activeBCProb (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (betaParams (boxCoupling J (2 * n)) beta) q)
    (innerCrossInd d n)




theorem weighted_outer_inner_hcov
    (d n : Nat) (hn : 1 <= n)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta D : Real) (hq : 1 <= q) (hbeta : 0 < beta) (hD : 0 < D)
    (hsum : forall i : (boxGraph d n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal
        (activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (betaParams (boxCoupling J (2 * n)) beta) q)
        (boxActiveEdgeLE d (n_le_two_mul n))
        (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
        (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D) :
    weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) / D <=
      ∑ e, Lindeberg.cov
        (activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (betaParams (boxCoupling J (2 * n)) beta) q)
        (innerCrossInd d n) (Lindeberg.coord e) := by
  classical
  let mu := activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (betaParams (boxCoupling J (2 * n)) beta) q
  let iota := boxActiveEdgeLE d (n_le_two_mul n)
  let disc0 : Nat -> Finset (Site d) := osssBoundaryFinset d
  let l : List (boxGraph d n).edgeSet :=
    (Finset.univ : Finset (boxGraph d n).edgeSet).toList
  have hl : forall i : (boxGraph d n).edgeSet, i ∈ l := by simp [l]
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
    intro k hk j
    simp
  have hcompute : forall (k : ↑(Finset.Icc 1 n))
      (omega : ConfigSpace (boxGraph d (2 * n)).edgeSet),
      (crossTree (boxActiveEndU d n) (boxActiveEndV d n) 0
        (vertexBoundary d n) l (disc0 (k : Nat))).evalR
          (restrictConfig iota omega) = innerCrossInd d n omega := by
    intro k omega
    have hk1 := (Finset.mem_Icc.mp k.2).1
    have hkn := (Finset.mem_Icc.mp k.2).2
    have heval := evalR_crossTree_connected
      (boxActiveEdge_injective d n) (boxActiveEdge_eq_endpoints d n)
      (boxActiveEnd_adj d n) (k : Nat) n hk1 hkn 0 (ho (k : Nat) hk1)
      l hl (disc0 (k : Nat)) (hdisc0sup (k : Nat)) (hoB (k : Nat))
      (restrictConfig iota omega)
    simpa [innerCrossInd, iota] using heval
  have hJbox : forall e : Sym2 (boxVerts d (2 * n)),
      0 < boxCoupling J (2 * n) e :=
    fun e => hJ (Sym2.map Subtype.val e)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmain := hcov_reindexed_crossTree_mass mu
    (activeBCProb_pos _ _ (betaParams_pos hJbox hbeta)
      (betaParams_lt_one _ beta) hq0)
    (activeBCProb_sum_eq_one _ _ (betaParams_pos hJbox hbeta)
      (betaParams_lt_one _ beta) hq0)
    (activeBCProb_FKGLatticeCondition _ _ (betaParams_pos hJbox hbeta)
      (betaParams_lt_one _ beta) hq)
    iota (boxActiveEdgeLE_injective d (n_le_two_mul n))
    (boxActiveEdge_injective d n) (boxActiveEdge_eq_endpoints d n)
    (boxActiveEnd_adj d n) 0 l hl disc0 hdisc0sub n hn
    (innerCrossInd d n) (innerCrossInd_monotone d n)
    (innerCrossInd_idem d n) hcompute D hD
    (by simpa [mu, iota] using hsum)
  simpa [weightedLocalizedTheta, mu] using hmain



theorem weighted_outer_inner_hcov_geom
    (d n : Nat) (hn : 1 <= n)
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) /
          weightedStrictDenom d n J q beta <=
      ∑ e, Lindeberg.cov
        (activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (betaParams (boxCoupling J (2 * n)) beta) q)
        (innerCrossInd d n) (Lindeberg.coord e) := by
  classical
  let mu := activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (betaParams (boxCoupling J (2 * n)) beta) q
  let iota := boxActiveEdgeLE d (n_le_two_mul n)
  let Lambda := osssBoxFinset d n
  let conn : Site d -> Nat -> Real := fun x j =>
    Lindeberg.mean mu (fun omega => if ConnectedToSet d
      (liftCfg (boxActiveEdge d n) (restrictConfig iota omega)) x
      (centeredBoundary x j) then (1 : Real) else 0)
  let M := Lambda.sup' ⟨0, origin_mem_osssBoxFinset d n⟩
    (fun x => ∑ j ∈ Finset.range n, conn x j)
  let D := 4 * M / (n : Real)
  have hJbox : forall e : Sym2 (boxVerts d (2 * n)),
      0 < boxCoupling J (2 * n) e :=
    fun e => hJ (Sym2.map Subtype.val e)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _ (betaParams_pos hJbox hbeta)
      (betaParams_lt_one _ beta) hq0 omega).le
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one _ _ (betaParams_pos hJbox hbeta)
      (betaParams_lt_one _ beta) hq0
  have hconn0 : forall x j, 0 <= conn x j := fun x j =>
    mean_indicator_nonneg hmu0 _
  have hMpos : 0 < M := by
    have hconnzero : conn 0 0 = 1 := by
      have hall : (fun omega : ConfigSpace (boxGraph d (2 * n)).edgeSet =>
          if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) (restrictConfig iota omega)) 0
            (centeredBoundary 0 0) then (1 : Real) else 0) = fun _ => 1 := by
        funext omega
        rw [if_pos]
        exact ⟨0, centeredRadius_self 0, connected_refl _ _⟩
      change Lindeberg.mean mu (fun omega => if ConnectedToSet d
        (liftCfg (boxActiveEdge d n) (restrictConfig iota omega)) 0
        (centeredBoundary 0 0) then (1 : Real) else 0) = 1
      rw [hall]
      exact Lindeberg.mean_const mu hmu1 1
    have hs : 1 <= ∑ j ∈ Finset.range n, conn 0 j := by
      rw [← hconnzero]
      apply Finset.single_le_sum (fun j _ => hconn0 0 j)
      simpa using hn
    have hsup := Finset.le_sup'
      (fun x => ∑ j ∈ Finset.range n, conn x j)
      (origin_mem_osssBoxFinset d n)
    change _ <= M at hsup
    linarith
  have hnR : (0 : Real) < n := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hDpos : 0 < D := by
    unfold D
    positivity
  have hsum : forall i : (boxGraph d n).edgeSet,
      (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal mu iota
        (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
        (k : Nat) i) <= (Fintype.card (↑(Finset.Icc 1 n)) : Real) * D := by
    intro i
    have hu := revealment_sum_bound_lattice_map mu hmu0
      (restrictConfig iota) (boxActiveEdge d n) Lambda
      ⟨0, origin_mem_osssBoxFinset d n⟩ (boxActiveEndU d n i)
      (boxActiveEndU_mem d n i) i.1.out.1.property
    have hv := revealment_sum_bound_lattice_map mu hmu0
      (restrictConfig iota) (boxActiveEdge d n) Lambda
      ⟨0, origin_mem_osssBoxFinset d n⟩ (boxActiveEndV d n i)
      (boxActiveEndV_mem d n i) i.1.out.2.property
    change _ <= 2 * M at hu
    change _ <= 2 * M at hv
    have hsplit :
        (∑ k : ↑(Finset.Icc 1 n), localizedBoxReveal mu iota
          (boxActiveEdge d n) (boxActiveEndU d n) (boxActiveEndV d n)
          (k : Nat) i) =
        (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean mu (fun omega =>
          if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) (restrictConfig iota omega))
            (boxActiveEndU d n i) (vertexBoundary d k)
          then (1 : Real) else 0)) +
        (∑ k ∈ Finset.Icc 1 n, Lindeberg.mean mu (fun omega =>
          if ConnectedToSet d
            (liftCfg (boxActiveEdge d n) (restrictConfig iota omega))
            (boxActiveEndV d n i) (vertexBoundary d k)
          then (1 : Real) else 0)) := by
      rw [Finset.sum_coe_sort (Finset.Icc 1 n)
        (fun k => localizedBoxReveal mu iota (boxActiveEdge d n)
          (boxActiveEndU d n) (boxActiveEndV d n) k i)]
      simp only [localizedBoxReveal, Finset.sum_add_distrib]
    have hncard : (Fintype.card (↑(Finset.Icc 1 n)) : Real) = n := by
      rw [Fintype.card_coe, Nat.card_Icc]
      norm_num
    rw [hsplit, hncard]
    change _ <= (n : Real) * (4 * M / (n : Real))
    have hright : (n : Real) * (4 * M / (n : Real)) = 4 * M := by
      field_simp
    rw [hright]
    change _ <= 4 * Lambda.sup' ⟨0, origin_mem_osssBoxFinset d n⟩
      (fun x => ∑ j ∈ Finset.range n, conn x j)
    linarith
  have hmain := weighted_outer_inner_hcov d n hn J hJ q beta D
    hq hbeta hDpos (by simpa [mu, iota] using hsum)
  simpa [weightedStrictDenom, weightedOuterInnerConn,
    weightedLocalizedTheta, mu, iota, Lambda, conn, M, D] using hmain

theorem weightedLocalizedTheta_nonneg
    (d n : Nat) (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    0 <= weightedLocalizedTheta d n J q beta := by
  unfold weightedLocalizedTheta Lindeberg.mean
  apply Finset.sum_nonneg
  intro omega homega
  apply mul_nonneg
  · unfold innerCrossInd crossIndG
    rw [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (activeBCProb_pos _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq) omega).le

theorem weightedLocalizedTheta_le_one
    (d n : Nat) (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedLocalizedTheta d n J q beta <= 1 := by
  let mu := activeBCProb (boxGraph d (2 * n))
    (wiredBoxBoundaryGraph d (2 * n))
    (betaParams (boxCoupling J (2 * n)) beta) q
  have hmu0 : forall omega, 0 <= mu omega := fun omega =>
    (activeBCProb_pos _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq) omega).le
  have hsum : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one _ _
      (betaParams_pos (fun e => hJ (Sym2.map Subtype.val e)) hbeta)
      (betaParams_lt_one _ beta) (zero_lt_one.trans_le hq)
  calc
    weightedLocalizedTheta d n J q beta <=
        Lindeberg.mean mu (fun _ => (1 : Real)) := by
      unfold weightedLocalizedTheta Lindeberg.mean
      apply Finset.sum_le_sum
      intro omega homega
      apply mul_le_mul_of_nonneg_right _ (hmu0 omega)
      unfold innerCrossInd crossIndG
      rw [Set.indicator_apply]
      split_ifs <;> norm_num
    _ = 1 := Lindeberg.mean_const mu hsum 1



theorem weighted_outer_inner_hcov_phaseEnvelope
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcov : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) /
          (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real)) <=
      ∑ e, Lindeberg.cov
        (activeBCProb (boxGraph d (2 * n))
          (wiredBoxBoundaryGraph d (2 * n))
          (betaParams (boxCoupling J (2 * n)) beta) q)
        (innerCrossInd d n) (Lindeberg.coord e) := by
  let theta := weightedLocalizedTheta d n J q beta
  have htheta0 : 0 <= theta :=
    weightedLocalizedTheta_nonneg d n J hJ q beta hq hbeta
  have htheta1 : theta <= 1 :=
    weightedLocalizedTheta_le_one d n J hJ q beta hq hbeta
  have hnum : 0 <= theta * (1 - theta) :=
    mul_nonneg htheta0 (sub_nonneg.mpr htheta1)
  have hDpos := weightedStrictDenom_pos d n hn J hJ q beta hq hbeta
  have hDle := weightedStrictDenom_le_phaseEnvelopeSig
    d n J hJ phase phaseJ hsurj hcov q beta hq hbeta
  have hfrac : theta * (1 - theta) /
      (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real)) <=
      theta * (1 - theta) / weightedStrictDenom d n J q beta :=
    div_le_div_of_nonneg_left hnum hDpos hDle
  exact hfrac.trans (by
    simpa [theta] using
      weighted_outer_inner_hcov_geom d n hn J hJ q beta hq hbeta)



theorem weighted_outer_inner_differential_phaseEnvelope
    (d n : Nat) (hd : 1 <= d) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real) (hJ : forall e, 0 < J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcovPhase : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    exists cR : Real, 0 < cR ∧
      cR * (weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) /
          (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (wiredBoxBoundaryGraph d (2 * n))
        (betaParams (boxCoupling J (2 * n)) b) q
        (innerCrossInd d n)) beta := by
  classical
  letI : Nonempty (boxGraph d (2 * n)).edgeSet :=
    boxGraph_edgeSet_nonempty d (2 * n) hd (by omega)
  let G := boxGraph d (2 * n)
  let C := wiredBoxBoundaryGraph d (2 * n)
  let Jbox := boxCoupling J (2 * n)
  let mu := activeBCProb G C (betaParams Jbox beta) q
  let f := innerCrossInd d n
  have hJbox : forall e, 0 < Jbox e :=
    fun e => hJ (Sym2.map Subtype.val e)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) /
          (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real)) <=
      ∑ e, activeBCCov G C (betaParams Jbox beta) q f
        (Lindeberg.coord e) := by
    simpa [G, C, Jbox, mu, f] using
      weighted_outer_inner_hcov_phaseEnvelope d n hn J hJ phase phaseJ
        hsurj hcovPhase q beta hq hbeta
  have hpos : forall omega, 0 < mu omega :=
    activeBCProb_pos G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    activeBCProb_FKGLatticeCondition G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq
  have hf : Monotone f := innerCrossInd_monotone d n
  have hcov0 : forall e : G.edgeSet,
      0 <= activeBCCov G C (betaParams Jbox beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← cov_activeBC_eq]
    exact cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := hasDerivAt_activeBCMean_beta_sum G C hJbox hbeta hq0 f
  have hderivEq :
      deriv (fun b => activeBCMean G C (betaParams Jbox b) q f) beta =
        ∑ e : G.edgeSet, (Jbox e.1 /
          (1 - Real.exp (-(beta * Jbox e.1)))) *
            activeBCCov G C (betaParams Jbox beta) q f
              (Lindeberg.coord e) := by
    simpa using hderiv.deriv
  obtain ⟨cR, hcR, hRusso⟩ :=
    rp_differential_lower_weighted_beta
      (fun e : G.edgeSet => Jbox e.1)
      (fun e => activeBCCov G C (betaParams Jbox beta) q f
        (Lindeberg.coord e)) beta
      (deriv (fun b => activeBCMean G C (betaParams Jbox b) q f) beta)
      (fun e => hJbox e.1) hbeta hcov0 hderivEq
  refine ⟨cR, hcR, ?_⟩
  have hmain := (mul_le_mul_of_nonneg_left hcov hcR.le).trans hRusso
  simpa [G, C, Jbox, mu, f] using hmain




theorem weighted_outer_inner_differential_phaseEnvelope_uniform
    (d n : Nat) (hn : 1 <= n)
    {P : Type*} [Fintype P] [Nonempty P]
    (J : Sym2 (Site d) -> Real)
    (Jmin : Real) (hJmin : 0 < Jmin)
    (hJlo : forall e, Jmin <= J e)
    (phase : Site d -> P) (phaseJ : P -> Sym2 (Site d) -> Real)
    (hsurj : Function.Surjective phase)
    (hcovPhase : PhaseCovariant J phase phaseJ)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta) :
    Jmin * (weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) /
          (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real))) <=
      deriv (fun b => activeBCMean (boxGraph d (2 * n))
        (wiredBoxBoundaryGraph d (2 * n))
        (betaParams (boxCoupling J (2 * n)) b) q
        (innerCrossInd d n)) beta := by
  classical
  let G := boxGraph d (2 * n)
  let C := wiredBoxBoundaryGraph d (2 * n)
  let Jbox := boxCoupling J (2 * n)
  let mu := activeBCProb G C (betaParams Jbox beta) q
  let f := innerCrossInd d n
  have hJbox : forall e, 0 < Jbox e := fun e =>
    hJmin.trans_le (hJlo (Sym2.map Subtype.val e))
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hcov : weightedLocalizedTheta d n J q beta *
        (1 - weightedLocalizedTheta d n J q beta) /
          (8 * weightedPhaseEnvelopeSig d n phaseJ q beta / (n : Real)) <=
      ∑ e, activeBCCov G C (betaParams Jbox beta) q f
        (Lindeberg.coord e) := by
    simpa [G, C, Jbox, mu, f] using
      weighted_outer_inner_hcov_phaseEnvelope d n hn J
        (fun e => hJmin.trans_le (hJlo e)) phase phaseJ
        hsurj hcovPhase q beta hq hbeta
  have hpos : forall omega, 0 < mu omega :=
    activeBCProb_pos G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq0
  have hmu1 : ∑ omega, mu omega = 1 :=
    activeBCProb_sum_eq_one G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq0
  have hFKG : FKGLatticeCondition mu :=
    activeBCProb_FKGLatticeCondition G C (betaParams_pos hJbox hbeta)
      (betaParams_lt_one Jbox beta) hq
  have hf : Monotone f := innerCrossInd_monotone d n
  have hcov0 : forall e : G.edgeSet,
      0 <= activeBCCov G C (betaParams Jbox beta) q f
        (Lindeberg.coord e) := by
    intro e
    rw [← cov_activeBC_eq]
    exact cov_coord_nonneg hpos hmu1 hFKG hf e
  have hderiv := hasDerivAt_activeBCMean_beta_sum G C hJbox hbeta hq0 f
  have hderivEq :
      deriv (fun b => activeBCMean G C (betaParams Jbox b) q f) beta =
        ∑ e : G.edgeSet, (Jbox e.1 /
          (1 - Real.exp (-(beta * Jbox e.1)))) *
            activeBCCov G C (betaParams Jbox beta) q f
              (Lindeberg.coord e) := by
    simpa using hderiv.deriv
  have hpref : forall e : G.edgeSet,
      Jmin <= Jbox e.1 / (1 - Real.exp (-(beta * Jbox e.1))) := by
    intro e
    have hden0 : 0 < 1 - Real.exp (-(beta * Jbox e.1)) := by
      have hexp := Real.exp_lt_one_iff.mpr
        (neg_lt_zero.mpr (mul_pos hbeta (hJbox e.1)))
      linarith
    rw [le_div_iff₀ hden0]
    have hden1 : 1 - Real.exp (-(beta * Jbox e.1)) <= 1 := by
      linarith [Real.exp_pos (-(beta * Jbox e.1))]
    calc
      Jmin * (1 - Real.exp (-(beta * Jbox e.1))) <= Jmin * 1 :=
        mul_le_mul_of_nonneg_left hden1 hJmin.le
      _ = Jmin := mul_one Jmin
      _ <= Jbox e.1 := hJlo (Sym2.map Subtype.val e.1)
  have hRusso : Jmin * ∑ e : G.edgeSet,
      activeBCCov G C (betaParams Jbox beta) q f (Lindeberg.coord e) <=
      deriv (fun b => activeBCMean G C (betaParams Jbox b) q f) beta := by
    rw [hderivEq]
    exact rp_prefactor_extraction _ _ Jmin hpref hcov0
  have hmain := (mul_le_mul_of_nonneg_left hcov hJmin.le).trans hRusso
  simpa [G, C, Jbox, mu, f] using hmain

end FKSharpnessWeightedLocalized
end OSSS
end StatMech

