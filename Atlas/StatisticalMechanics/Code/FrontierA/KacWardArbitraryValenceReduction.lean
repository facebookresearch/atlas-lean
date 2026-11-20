/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardPortChainEvenPolynomial
import Code.FrontierA.KacWardPolygonGlobalReduction











namespace StatMech.FrontierA

open SimpleGraph
open Finset Polynomial
open StatMech.Onsager
open scoped BigOperators




noncomputable def kwDetOneSubWith
    {D : Type*} [Fintype D] (decEq : DecidableEq D)
    (M : Matrix D D Complex) : Complex :=
  @Matrix.det D decEq _ Complex _
    ((@Matrix.one D Complex decEq _ _).one - M)

theorem kwDetOneSubWith_eq
    {D : Type*} [Fintype D] (decEq decEq' : DecidableEq D)
    (M : Matrix D D Complex) :
    kwDetOneSubWith decEq M = kwDetOneSubWith decEq' M := by
  have h : decEq = decEq' := Subsingleton.elim _ _
  subst decEq'
  rfl





theorem kacWard_allWeights_of_formalRoot_eq_evenPolynomial
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (hformal : kwGraphFormalRoot G phase =
      kwGraphFormalEvenPolynomial G)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  let originalDartDecEq : DecidableEq G.Dart := inferInstance
  let standardDartDecEq : DecidableEq G.Dart :=
    fun a b => SimpleGraph.instDecidableEqDart a b
  letI : DecidableEq G.Dart := standardDartDecEq
  let M := kwGraphTransition G weight phase
  let P := kwDetScalePolynomial M
  let Q := (kwEvenScalePolynomial G weight) ^ 2
  let card : Real := Fintype.card G.Dart
  let q : Real := (2 * (1 + card))⁻¹
  let B : Real := ∑ dart : G.Dart, ∑ next : G.Dart,
    norm (M dart next)
  let delta : Real := q / (1 + B)
  have hcard0 : 0 <= card := by positivity
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
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
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    have hrnorm : norm (r : Complex) = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    let scaled : Sym2 V -> Complex := fun edge => (r : Complex) * weight edge
    have hentry : forall dart next,
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
        StatMech.Onsager.ons_detWalkRoot
            (kwGraphTransition G scaled phase) =
          kwEvenPolynomial G scaled := by
      rw [← kw_mvSeriesEval_GraphFormalRoot
          G phase scaled q hq.le hentry hcardq,
        hformal, kwGraphFormalEvenPolynomial_eval]
    have hsmall :
        (1 - kwGraphTransition G scaled phase).det =
          (kwEvenPolynomial G scaled) ^ 2 := by
      calc
        (1 - kwGraphTransition G scaled phase).det =
            StatMech.Onsager.ons_detWalkRoot
              (kwGraphTransition G scaled phase) ^ 2 :=
          (StatMech.Onsager.ons_detWalkRoot_sq
            (kwGraphTransition G scaled phase) hspec).symm
        _ = (kwEvenPolynomial G scaled) ^ 2 := by rw [hroot]
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval,
      Polynomial.eval_pow, kwEvenScalePolynomial_eval]
    have hmatrix : (r : Complex) • M =
        kwGraphTransition G scaled phase := by
      ext dart next
      change (r : Complex) * M dart next = _
      dsimp only [M, scaled]
      rw [kwGraphTransition_smulWeight]
    rw [hmatrix]
    exact hsmall
  have hinfinite : Set.Infinite
      {z : Complex | P.eval z = Q.eval z} := by
    have hI : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real => (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hI.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q :=
    Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  have hone' : kwDetOneSubWith standardDartDecEq M =
      (kwEvenPolynomial G weight) ^ 2 := by
    simpa [kwDetOneSubWith, kwDetScalePolynomial_eval,
      kwEvenScalePolynomial_eval, M] using hone
  change kwDetOneSubWith originalDartDecEq M =
    (kwEvenPolynomial G weight) ^ 2
  exact (kwDetOneSubWith_eq originalDartDecEq standardDartDecEq M).trans hone'



theorem kacWard_allWeights_of_unitCycleLog
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (hunit : KWGraphUnitCycleLog G phase)
    (hdeg : forall vertex, G.degree vertex <= 3)
    (hnonsquare : forall m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  kacWard_allWeights_of_formalRoot_eq_evenPolynomial G phase
    (kwGraphFormalRoot_eq_evenPolynomial_of_unitCycleLog
      G phase hunit hdeg hnonsquare) weight


theorem kwAngularSplit_degree_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (p : KWDartPort G) :
    (kwOrderedDartPortSplitGraph G
      (kwAngularPortOrder embedding)).degree p <= 3 :=
  kwOrderedDartPortSplitGraph_degree_le_three G
    (kwAngularPortOrder embedding) p




theorem kacWard_original_iff_angularSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
        (kwEvenPolynomial G weight) ^ 2 <->
      (1 - kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding)).det =
        (kwEvenPolynomial
          (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
          (kwOrderedSplitWeight G weight)) ^ 2 := by
  rw [kwAngularSplit_det_eq_original embedding weight,
    kwOrderedSplit_evenPolynomial_eq G (kwAngularPortOrder embedding) weight]




theorem kacWard_original_of_angularSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V -> Complex)
    (hsplit :
      (1 - kwGraphTransition
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        (kwOrderedSplitWeight G weight)
        (kwAngularSplitPhase embedding)).det =
        (kwEvenPolynomial
          (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
          (kwOrderedSplitWeight G weight)) ^ 2) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 :=
  (kacWard_original_iff_angularSplit embedding weight).2 hsplit




theorem kacWard_original_of_angularSplit_unitCycleLog
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (weight : Sym2 V -> Complex)
    (hunit : KWGraphUnitCycleLog
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwAngularSplitPhase embedding))
    (hnonsquare : forall m : Sym2 (KWDartPort G) →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m
          (kwGraphFormalRoot
            (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
            (kwAngularSplitPhase embedding)) = 0) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      (kwEvenPolynomial G weight) ^ 2 := by
  apply kacWard_original_of_angularSplit embedding weight
  have hs := kacWard_allWeights_of_unitCycleLog
    (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
    (kwAngularSplitPhase embedding) hunit
    (kwAngularSplit_degree_le_three embedding) hnonsquare
    (kwOrderedSplitWeight G weight)
  exact hs

end StatMech.FrontierA
