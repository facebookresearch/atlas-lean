/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.SurfaceKacWardQuadraticAssembly
import Code.FrontierA.SurfaceKacWardFlatSpinor
import Code.FrontierA.KacWardAngularSplitUnitCycleReduction
import Code.FrontierA.KacWardPortChainHomology
import Code.FrontierA.KacWardLocalAngularSplitCycleReversal









open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

noncomputable def surfaceSpinCycleCoefficient {g : Nat} {V : Type u}
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (S : Finset (Sym2 V)) : Complex :=
  (surfaceParitySign
    (surfaceQuadraticParity lambda
      (surfaceSubgraphHomology edgeClass S)) : Real)

theorem kwGraphFormalRoot_coeff_surfaceQuadratic_shifted
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (S : Finset (Sym2 V)) (hS : S ∈ evenSubgraphs G) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (kwGraphFormalRoot G phase) =
      (surfaceParitySign
        (surfaceQuadraticParity lambda
          (surfaceSubgraphHomology edgeClass S)) : Complex) := by
  classical
  obtain ⟨I, hI, hdecI, base, cycle, hcycle, hcover,
      hedgeDisjoint, hvertDisjoint, hcoeff⟩ :=
    kwGraphFormalRoot_coeff_evenSubgraph_of_weightedCycleLog
      G phase (surfaceSpinCycleCoefficient edgeClass lambda)
        hlog hdeg S hS
  letI : Fintype I := hI
  letI : DecidableEq I := hdecI
  rw [hcoeff]
  let homology : I -> SurfaceHomology g := fun i =>
    surfaceSubgraphHomology edgeClass (cycle i).edges.toFinset
  have hpair : ∀ i ∈ (Finset.univ : Finset I),
      ∀ j ∈ (Finset.univ : Finset I), i ≠ j ->
        surfaceIntersection (homology i) (homology j) = 0 := by
    intro i hi j hj hij
    exact hisotropic (cycle i) (cycle j) (hcycle i) (hcycle j)
      (hvertDisjoint hi hj hij)
  have hsign :=
    surfaceParitySign_quadratic_finset_sum_of_pairwise_intersection_zero
      lambda Finset.univ homology hpair
  have hhomology : surfaceSubgraphHomology edgeClass S = ∑ i, homology i := by
    exact surfaceSubgraphHomology_biUnion edgeClass S
      (fun i => (cycle i).edges.toFinset) hcover hedgeDisjoint
  unfold surfaceSpinCycleCoefficient homology at *
  simpa only [hhomology] using hsign.symm

noncomputable def surfaceSpinFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) :
    MvPowerSeries (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPowerSeries.monomial (ons_finsetExponent F)
      (surfaceSpinCycleCoefficient edgeClass lambda F)

noncomputable def surfaceSpinEvenMvPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) :
    MvPolynomial (Sym2 V) Complex :=
  ∑ F ∈ evenSubgraphs G,
    MvPolynomial.monomial (ons_finsetExponent F)
      (surfaceSpinCycleCoefficient edgeClass lambda F)

theorem surfaceSpinFormalEvenPolynomial_eq_coe
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) :
    surfaceSpinFormalEvenPolynomial G edgeClass lambda =
      (surfaceSpinEvenMvPolynomial G edgeClass lambda :
        MvPowerSeries (Sym2 V) Complex) := by
  classical
  unfold surfaceSpinFormalEvenPolynomial surfaceSpinEvenMvPolynomial
  ext m
  rw [map_sum, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
  simp [eq_comm]

theorem surfaceSpinFormalEvenPolynomial_coeff_finsetExponent
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (S : Finset (Sym2 V)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (surfaceSpinFormalEvenPolynomial G edgeClass lambda) =
      if S ∈ evenSubgraphs G then
        surfaceSpinCycleCoefficient edgeClass lambda S else 0 := by
  classical
  unfold surfaceSpinFormalEvenPolynomial
  rw [map_sum]
  by_cases hS : S ∈ evenSubgraphs G
  · rw [Finset.sum_eq_single S]
    · simp [hS]
    · intro T hT hTS
      rw [MvPowerSeries.coeff_monomial, if_neg]
      intro heq
      exact hTS (ons_finsetExponent_injective heq.symm)
    · exact fun hnot => (hnot hS).elim
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro T hT
    rw [MvPowerSeries.coeff_monomial, if_neg]
    intro heq
    apply hS
    rw [ons_finsetExponent_injective heq]
    exact hT

theorem surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (m : Sym2 V →₀ Nat) (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
        (surfaceSpinFormalEvenPolynomial G edgeClass lambda) = 0 := by
  classical
  unfold surfaceSpinFormalEvenPolynomial
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [MvPowerSeries.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [heq, ons_finsetExponent_apply]
  split <;> omega

theorem kwGraphFormalRoot_eq_surfaceSpinFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
    kwGraphFormalRoot G phase =
      surfaceSpinFormalEvenPolynomial G edgeClass lambda := by
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    by_cases heven : m.support ∈ evenSubgraphs G
    · rw [kwGraphFormalRoot_coeff_surfaceQuadratic_shifted
        G phase edgeClass lambda hlog hisotropic hdeg m.support heven,
        surfaceSpinFormalEvenPolynomial_coeff_finsetExponent,
        if_pos heven]
      rfl
    · rw [kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted
        G phase _ hlog m.support heven,
        surfaceSpinFormalEvenPolynomial_coeff_finsetExponent,
        if_neg heven]
  · rw [hnonsquare m hm,
      surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
        G edgeClass lambda m hm]

theorem surfaceSpinEvenMvPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) :
    MvPolynomial.eval weight
        (surfaceSpinEvenMvPolynomial G edgeClass lambda) =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  classical
  unfold surfaceSpinEvenMvPolynomial surfaceQuadraticEvenPolynomial
    surfaceSpinCycleCoefficient evenSubgraphs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod]

theorem surfaceSpinFormalEvenPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) :
    ons_mvSeriesEval (surfaceSpinFormalEvenPolynomial G edgeClass lambda)
        weight =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  rw [surfaceSpinFormalEvenPolynomial_eq_coe, ons_mvSeriesEval_coe,
    surfaceSpinEvenMvPolynomial_eval]

noncomputable def surfaceSpinScalePolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) : Polynomial Complex :=
  ∑ F ∈ evenSubgraphs G,
    Polynomial.monomial F.card
      (surfaceSpinCycleCoefficient edgeClass lambda F *
        ∏ edge ∈ F, weight edge)

theorem surfaceSpinScalePolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) (t : Complex) :
    (surfaceSpinScalePolynomial G edgeClass lambda weight).eval t =
      surfaceQuadraticEvenPolynomial G edgeClass lambda
        (fun edge => t * weight edge) := by
  classical
  unfold surfaceSpinScalePolynomial surfaceQuadraticEvenPolynomial
    surfaceSpinCycleCoefficient evenSubgraphs
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib]
  simp
  ring



theorem surface_kacWard_shifted_det_square_of_cycle_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  let originalDartDecEq : DecidableEq G.Dart := inferInstance
  let standardDartDecEq : DecidableEq G.Dart :=
    fun a b => SimpleGraph.instDecidableEqDart a b
  letI : DecidableEq G.Dart := standardDartDecEq
  let M := kwGraphTransition G weight phase
  let P := kwDetScalePolynomial M
  let Q := (surfaceSpinScalePolynomial G edgeClass lambda weight) ^ 2
  let card : Real := Fintype.card G.Dart
  let q : Real := (2 * (1 + card))⁻¹
  let B : Real := ∑ dart : G.Dart, ∑ next : G.Dart, norm (M dart next)
  let delta : Real := q / (1 + B)
  have hcard0 : 0 <= card := by positivity
  have hq : 0 < q := by dsimp only [q]; positivity
  have hB : 0 <= B := by dsimp only [B]; positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hcardq : card * q < 1 := by
    dsimp only [q]
    rw [mul_inv_lt_iff₀ (by positivity : 0 < 2 * (1 + card))]
    nlinarith
  have hraw (dart next : G.Dart) : norm (M dart next) <= B := by
    dsimp only [B]
    exact (Finset.single_le_sum
      (fun d _ => Finset.sum_nonneg fun e _ => norm_nonneg (M d e))
      (Finset.mem_univ dart)).trans' <|
        Finset.single_le_sum
          (fun e _ => norm_nonneg (M dart e)) (Finset.mem_univ next)
  have hformal := kwGraphFormalRoot_eq_surfaceSpinFormalEvenPolynomial
    G phase edgeClass lambda hlog hisotropic hdeg hnonsquare
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    have hrnorm : norm (r : Complex) = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    let scaled : Sym2 V -> Complex := fun edge => (r : Complex) * weight edge
    have hentry : ∀ dart next,
        norm (kwGraphTransition G scaled phase dart next) <= q := by
      intro dart next
      rw [show scaled = fun edge => (r : Complex) * weight edge from rfl,
        kwGraphTransition_smulWeight, norm_mul, hrnorm]
      have hlt : r * B < q := by
        have hden : 0 < 1 + B := by positivity
        have h := hr.2
        dsimp only [delta] at h
        rw [lt_div_iff₀ hden] at h
        nlinarith
      exact (mul_le_mul_of_nonneg_left
        (hraw dart next) hr.1.le).trans hlt.le
    have hspec : ∀ alpha ∈
        (kwGraphTransition G scaled phase).charpoly.roots,
        norm alpha < 1 :=
      ons_spectral_lt_one_of_entry
        (kwGraphTransition G scaled phase) q hq.le hentry hcardq
    have hroot :
        ons_detWalkRoot (kwGraphTransition G scaled phase) =
          surfaceQuadraticEvenPolynomial G edgeClass lambda scaled := by
      rw [<- kw_mvSeriesEval_GraphFormalRoot
          G phase scaled q hq.le hentry hcardq,
        hformal, surfaceSpinFormalEvenPolynomial_eval]
    have hsmall :
        (1 - kwGraphTransition G scaled phase).det =
          surfaceQuadraticEvenPolynomial G edgeClass lambda scaled ^ 2 := by
      calc
        (1 - kwGraphTransition G scaled phase).det =
            ons_detWalkRoot (kwGraphTransition G scaled phase) ^ 2 :=
          (ons_detWalkRoot_sq
            (kwGraphTransition G scaled phase) hspec).symm
        _ = _ := by rw [hroot]
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
      surfaceSpinScalePolynomial_eval]
    have hmatrix : (r : Complex) • M =
        kwGraphTransition G scaled phase := by
      ext dart next
      change (r : Complex) * M dart next = _
      dsimp only [M, scaled]
      rw [kwGraphTransition_smulWeight]
    rw [hmatrix]
    exact hsmall
  have hinfinite : Set.Infinite {z : Complex | P.eval z = Q.eval z} := by
    have hI : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real => (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hI.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  have hone' : kwDetOneSubWith standardDartDecEq M =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
    simpa [kwDetOneSubWith, kwDetScalePolynomial_eval,
      surfaceSpinScalePolynomial_eval, M] using hone
  change kwDetOneSubWith originalDartDecEq M =
    surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2
  exact (kwDetOneSubWith_eq originalDartDecEq standardDartDecEq M).trans hone'

def KWGraphShiftedSimpleCyclePhase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) : Prop :=
  ∀ {root : V} (p : G.Walk root root), (hp : p.IsCycle) ->
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
      -surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset

theorem kwGraphFormalLogCoeff_cycle_of_shifted_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
        -surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset) :
    kwGraphFormalLogCoeff G phase (ons_finsetExponent p.edges.toFinset) =
      surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let coefficient :=
    surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset
  have hscalar : kwGraphLoopScalar G phase (kwGraphCycleDartLoop p) =
      -coefficient := by
    rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct G phase p hp]
    exact hphase
  have hcoeffNe : coefficient ≠ 0 := by
    unfold coefficient surfaceSpinCycleCoefficient
    exact Complex.ofReal_ne_zero.mpr (surfaceParitySign_ne_zero _)
  have hscalarNe : kwGraphLoopScalar G phase
      (kwGraphCycleDartLoop p) ≠ 0 := by
    rw [hscalar]
    exact neg_ne_zero.mpr hcoeffNe
  have hd : kwGraphCycleDartLoop p ∈
      kwGraphSquarefreeLoopFinset G phase p.edges.toFinset := by
    rw [kwGraph_mem_squarefreeLoopFinset]
    exact ⟨kwGraphCycleDartLoop_exponent G p hp, hscalarNe⟩
  rw [kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant'
    G phase hrev hdeg p.edges.toFinset (kwGraphCycleDartLoop p) hd,
    hscalar]
  ring

theorem kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hphase : KWGraphShiftedSimpleCyclePhase
      G phase edgeClass lambda) :
    KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda) := by
  constructor
  · intro root p hp
    exact kwGraphFormalLogCoeff_cycle_of_shifted_phase
      G phase edgeClass lambda hrev hdeg p hp (hphase p hp)
  · exact kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero
      G phase hdeg

theorem surface_kacWard_shifted_det_square_of_simpleCyclePhase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hphase : KWGraphShiftedSimpleCyclePhase
      G phase edgeClass lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  apply surface_kacWard_shifted_det_square_of_cycle_phase
    G phase edgeClass lambda
  · exact kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase
      G phase edgeClass lambda hrev hdeg hphase
  · exact hisotropic
  · exact hdeg
  · exact hnonsquare

def KWAngularSplitShiftedCyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1) : Prop :=
  KWGraphShiftedSimpleCyclePhase
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwAngularSplitPhase embedding) edgeClass lambda

theorem kwAngularSplit_shifted_det_square_of_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1)
    (hphase : KWAngularSplitShiftedCyclePhase
      embedding edgeClass lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      edgeClass)
    (weight : Sym2 (KWDartPort G) -> Complex) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      weight (kwAngularSplitPhase embedding)).det =
      surfaceQuadraticEvenPolynomial
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        edgeClass lambda weight ^ 2 := by
  apply surface_kacWard_shifted_det_square_of_simpleCyclePhase
  · exact kwAngularSplit_loopReversalInvariant embedding
  · exact hphase
  · exact hisotropic
  · exact kwAngularSplit_degree_le_three embedding
  · exact kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree embedding



theorem surface_kacWard_original_of_angularSplit_shifted_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (edgeClass : Sym2 V -> SurfaceHomology 1)
    (hdiag : ∀ v, edgeClass s(v, v) = 0)
    (lambda : SurfaceSpinStructure 1)
    (weight : Sym2 V -> Complex)
    (hphase : KWAngularSplitShiftedCyclePhase embedding
      (kwOrderedSplitEdgeClass edgeClass) lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwOrderedSplitEdgeClass edgeClass)) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  rw [<- kwAngularSplit_det_eq_original embedding weight]
  rw [← kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq
    G (kwAngularPortOrder embedding) edgeClass hdiag lambda weight]
  exact kwAngularSplit_shifted_det_square_of_cyclePhase embedding
    (kwOrderedSplitEdgeClass edgeClass) lambda hphase hisotropic
    (kwOrderedSplitWeight G weight)



def KWLocalAngularSplitShiftedCyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1) : Prop :=
  KWGraphShiftedSimpleCyclePhase
    (kwOrderedDartPortSplitGraph G data.order)
    (kwLocalAngularSplitPhase data) edgeClass lambda

theorem kwLocalAngularSplit_shifted_det_square_of_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1)
    (hphase : KWLocalAngularSplitShiftedCyclePhase
      data edgeClass lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G data.order) edgeClass)
    (weight : Sym2 (KWDartPort G) -> Complex) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G data.order)
      weight (kwLocalAngularSplitPhase data)).det =
      surfaceQuadraticEvenPolynomial
        (kwOrderedDartPortSplitGraph G data.order)
        edgeClass lambda weight ^ 2 := by
  apply surface_kacWard_shifted_det_square_of_simpleCyclePhase
  · exact kwLocalAngularSplit_loopReversalInvariant data
  · exact hphase
  · exact hisotropic
  · exact kwOrderedDartPortSplitGraph_degree_le_three G data.order
  · exact kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree data



theorem surface_kacWard_original_of_localAngularSplit_shifted_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (edgeClass : Sym2 V -> SurfaceHomology 1)
    (hdiag : forall v, edgeClass s(v, v) = 0)
    (lambda : SurfaceSpinStructure 1)
    (weight : Sym2 V -> Complex)
    (hphase : KWLocalAngularSplitShiftedCyclePhase data
      (kwOrderedSplitEdgeClass edgeClass) lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G data.order)
      (kwOrderedSplitEdgeClass edgeClass)) :
    (1 - kwGraphTransition G weight data.phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  rw [<- kwLocalAngularSplit_det_eq_original data weight]
  rw [← kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq
    G data.order edgeClass hdiag lambda weight]
  exact kwLocalAngularSplit_shifted_det_square_of_cyclePhase data
    (kwOrderedSplitEdgeClass edgeClass) lambda hphase hisotropic
    (kwOrderedSplitWeight G weight)

end StatMech.FrontierA
