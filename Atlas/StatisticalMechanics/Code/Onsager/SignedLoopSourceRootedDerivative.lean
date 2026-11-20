/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Onsager.SignedLoopAddedEdgeRooted
import Code.Onsager.SignedLoopHighTempResummation





open scoped BigOperators
open Filter SimpleGraph

namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section




theorem derivative_eq_source_of_eventually_sq_eq_sq
    (root : Complex -> Complex) (base source rootDeriv : Complex)
    (hroot : HasDerivAt root rootDeriv 0)
    (hzero : root 0 = base) (hbase : base ≠ 0)
    (hsq : (fun t => root t ^ 2) =ᶠ[nhds 0]
      (fun t => (base + t * source) ^ 2)) :
    rootDeriv = source := by
  let affine : Complex -> Complex := fun t => base + t * source
  have haffine : HasDerivAt affine source 0 := by
    dsimp only [affine]
    convert (hasDerivAt_const (x := (0 : Complex)) base).add
      ((hasDerivAt_id (x := (0 : Complex))).mul_const source) using 1
    all_goals ring
  have hsq' : (fun t => root t * root t) =ᶠ[nhds 0]
      (fun t => affine t * affine t) := by
    filter_upwards [hsq] with t ht
    simpa [pow_two, affine] using ht
  have hderiv := ((hroot.mul hroot).congr_of_eventuallyEq hsq'.symm).unique
    (haffine.mul haffine)
  dsimp only [affine] at hderiv
  rw [hzero] at hderiv
  have htwo : (2 : Complex) * base ≠ 0 :=
    mul_ne_zero (by norm_num) hbase
  apply mul_left_cancel₀ htwo
  linear_combination hderiv

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]



def ons_kwAddedEdgeEvenBase
    (weight : Sym2 V -> Complex) (selected : G.Dart) : Complex :=
  kwEvenPolynomial G
    (kwScaleGraphEdgeWeight weight selected.edge 0)



def ons_kwAddedEdgeEvenSource
    (weight : Sym2 V -> Complex) (selected : G.Dart) : Complex :=
  weight selected.edge *
    ons_kwEvenEdgeCoefficient G weight selected.edge



def ons_kwAddedEdgeNormalizedSource
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart) : Complex :=
  ons_kwAddedEdgeEvenBase G weight selected /
      ons_kwAddedEdgeRoot G embedding weight selected 0 *
    ons_kwAddedEdgeEvenSource G weight selected



theorem kwEvenPolynomial_scaleGraphEdge_affine
    (weight : Sym2 V -> Complex) (selected : G.Dart) (t : Complex) :
    kwEvenPolynomial G
        (kwScaleGraphEdgeWeight weight selected.edge t) =
      ons_kwAddedEdgeEvenBase G weight selected +
        t * ons_kwAddedEdgeEvenSource G weight selected := by
  have ht : kwScaleGraphEdgeWeight weight selected.edge t =
      ons_setGraphEdgeWeight weight selected.edge
        (t * weight selected.edge) := by
    funext edge
    by_cases hedge : edge = selected.edge <;>
      simp [kwScaleGraphEdgeWeight, ons_setGraphEdgeWeight, hedge]
  have hzero : kwScaleGraphEdgeWeight weight selected.edge 0 =
      ons_setGraphEdgeWeight weight selected.edge 0 := by
    funext edge
    by_cases hedge : edge = selected.edge <;>
      simp [kwScaleGraphEdgeWeight, ons_setGraphEdgeWeight, hedge]
  rw [ht, kwEvenPolynomial_setEdge_affine]
  unfold ons_kwAddedEdgeEvenBase ons_kwAddedEdgeEvenSource
  rw [hzero]
  ring



theorem ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : Real) * q < 1)
    (t : Complex) (ht : ‖t‖ ≤ 1) :
    ons_kwAddedEdgeRoot G embedding weight selected t ^ 2 =
      kwEvenPolynomial G
        (kwScaleGraphEdgeWeight weight selected.edge t) ^ 2 := by
  let scaledWeight := kwScaleGraphEdgeWeight weight selected.edge t
  let M := kwGraphTransition G scaledWeight embedding.turnPhase
  have hentryScaled : ∀ dart next, ‖M dart next‖ ≤ q := by
    intro dart next
    dsimp only [M, scaledWeight]
    rw [kwGraphTransition_scaleEdge_entry]
    by_cases hedge : dart.edge = selected.edge
    · rw [if_pos hedge, norm_mul]
      calc
        ‖t‖ * ‖kwGraphTransition G weight embedding.turnPhase dart next‖ ≤
            1 * q := mul_le_mul ht (hentry dart next)
              (norm_nonneg _) (by positivity)
        _ = q := one_mul q
    · rw [if_neg hedge, one_mul]
      exact hentry dart next
  have hspec : ∀ alpha ∈ M.charpoly.roots, ‖alpha‖ < 1 :=
    ons_spectral_lt_one_of_entry M q hq hentryScaled hcard
  calc
    ons_kwAddedEdgeRoot G embedding weight selected t ^ 2 =
        (1 - M).det := by
      exact ons_detWalkRoot_sq M hspec
    _ = kwEvenPolynomial G scaledWeight ^ 2 :=
      kacWard_straightLine_arbitrary_adaptive G embedding scaledWeight

theorem ons_kwAddedEdgeRoot_zero_ne
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart) :
    ons_kwAddedEdgeRoot G embedding weight selected 0 ≠ 0 := by
  unfold ons_kwAddedEdgeRoot ons_detWalkRoot
  exact Complex.exp_ne_zero _



theorem ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : Real) * q < 1)
    (t : Complex) (ht : ‖t‖ ≤ 1) :
    ons_kwAddedEdgeRoot G embedding weight selected t ^ 2 =
      (ons_kwAddedEdgeRoot G embedding weight selected 0 +
        t * ons_kwAddedEdgeNormalizedSource G embedding weight selected) ^ 2 := by
  let R := ons_kwAddedEdgeRoot G embedding weight selected 0
  let A := ons_kwAddedEdgeEvenBase G weight selected
  let B := ons_kwAddedEdgeEvenSource G weight selected
  have hR : R ≠ 0 := ons_kwAddedEdgeRoot_zero_ne G embedding weight selected
  have hzeroSq := ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq
    G embedding weight selected q hq hentry hcard 0 (by simp)
  have hRA : R ^ 2 = A ^ 2 := by
    simpa only [R, A, kwEvenPolynomial_scaleGraphEdge_affine,
      zero_mul, add_zero] using hzeroSq
  rw [ons_kwAddedEdgeRoot_sq_eq_evenPolynomial_sq
    G embedding weight selected q hq hentry hcard t ht,
    kwEvenPolynomial_scaleGraphEdge_affine]
  change (A + t * B) ^ 2 = (R + t * (A / R * B)) ^ 2
  field_simp [hR]
  rw [hRA]
  ring



theorem eventually_ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : Real) * q < 1) :
    (fun t => ons_kwAddedEdgeRoot G embedding weight selected t ^ 2) =ᶠ[nhds 0]
      (fun t => (ons_kwAddedEdgeRoot G embedding weight selected 0 +
        t * ons_kwAddedEdgeNormalizedSource G embedding weight selected) ^ 2) := by
  filter_upwards [Metric.ball_mem_nhds (0 : Complex)
    (by norm_num : (0 : Real) < 1)] with t ht
  rw [Metric.mem_ball, dist_zero_right] at ht
  exact ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq
    G embedding weight selected q hq hentry hcard t ht.le




theorem ons_source_eq_neg_deleted_mul_rooted_of_local_square
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : Real) * q < 1)
    (base source : Complex)
    (hzero : ons_kwAddedEdgeRoot G embedding weight selected 0 = base)
    (hbase : base ≠ 0)
    (hsq : (fun t =>
        ons_kwAddedEdgeRoot G embedding weight selected t ^ 2) =ᶠ[nhds 0]
      (fun t => (base + t * source) ^ 2)) :
    source = -(ons_kwAddedEdgeDeletedRoot G embedding weight selected *
      ons_kwAddedEdgeRootedSeries G embedding weight selected) := by
  have hderiv := hasDerivAt_ons_kwAddedEdgeRoot_zero G embedding weight
    selected q hq hentry hsmall hcard
  exact (derivative_eq_source_of_eventually_sq_eq_sq
    (ons_kwAddedEdgeRoot G embedding weight selected)
    base source
    (-(ons_kwAddedEdgeDeletedRoot G embedding weight selected *
      ons_kwAddedEdgeRootedSeries G embedding weight selected))
    hderiv hzero hbase hsq).symm



theorem ons_kwAddedEdgeNormalizedSource_eq_neg_deleted_mul_rooted
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V -> Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : Real) * q < 1) :
    ons_kwAddedEdgeNormalizedSource G embedding weight selected =
      -(ons_kwAddedEdgeDeletedRoot G embedding weight selected *
        ons_kwAddedEdgeRootedSeries G embedding weight selected) := by
  exact ons_source_eq_neg_deleted_mul_rooted_of_local_square
    G embedding weight selected q hq hentry hsmall hcard
    (ons_kwAddedEdgeRoot G embedding weight selected 0)
    (ons_kwAddedEdgeNormalizedSource G embedding weight selected)
    rfl (ons_kwAddedEdgeRoot_zero_ne G embedding weight selected)
    (eventually_ons_kwAddedEdgeRoot_sq_eq_normalizedSource_sq
      G embedding weight selected q hq hentry hcard)

end

end StatMech.Onsager
