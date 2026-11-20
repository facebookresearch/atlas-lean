/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.KacWardStraightLineDeletion












open scoped BigOperators
open Finset SimpleGraph Filter

namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ons_kwAddedEdgeBaseMatrix
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) : Matrix G.Dart G.Dart Complex :=
  kwGraphTransition G weight embedding.turnPhase


def ons_kwAddedEdgeRoot
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart)
    (t : Complex) : Complex :=
  ons_detWalkRoot
    (kwGraphTransition G
      (kwScaleGraphEdgeWeight weight selected.edge t)
      embedding.turnPhase)



def ons_kwAddedEdgeDeletedRoot
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart) : Complex :=
  ons_detWalkRoot
    (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
      (ons_kwAddedEdgeBaseMatrix G embedding weight))




def ons_kwAddedEdgeRootedSeries
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart) : Complex :=
  ∑' path : List G.Dart,
    ons_firstReturnWeight (ons_kwAddedEdgeBaseMatrix G embedding weight)
      selected selected.symm path



theorem summable_norm_ons_kwAddedEdgeRootedSeries
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hcard : (Fintype.card G.Dart : Real) * q < 1) :
    Summable (fun path : List G.Dart ↦
      ‖ons_firstReturnWeight (ons_kwAddedEdgeBaseMatrix G embedding weight)
        selected selected.symm path‖) :=
  ons_firstReturnWeight_converges
    (ons_kwAddedEdgeBaseMatrix G embedding weight)
    selected selected.symm q hq hentry hcard

private theorem norm_scaleColumns_le_of_norm_le_one
    {E : Type*} [DecidableEq E]
    (S : Finset E) (t : Complex) (M : Matrix E E Complex)
    (q : Real) (ht : ‖t‖ ≤ 1)
    (hentry : ∀ i j, ‖M i j‖ ≤ q) (i j : E) :
    ‖ons_scaleColumns S t M i j‖ ≤ q := by
  unfold ons_scaleColumns
  by_cases hj : j ∈ S
  · rw [if_pos hj, norm_mul]
    calc
      ‖t‖ * ‖M i j‖ ≤ 1 * q :=
        mul_le_mul ht (hentry i j) (norm_nonneg _) (by positivity)
      _ = q := one_mul q
  · simpa [hj] using hentry i j



theorem ons_kwAddedEdgeRoot_eq_deleted_mul_rooted
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : Real) * q < 1)
    (t : Complex) (ht : ‖t‖ ≤ 1) :
    ons_kwAddedEdgeRoot G embedding weight selected t =
      ons_kwAddedEdgeDeletedRoot G embedding weight selected *
        (1 - t * ons_kwAddedEdgeRootedSeries G embedding weight selected) := by
  apply kwStraightLineGraph_detWalkRoot_scaleEdge_affine
    G embedding weight selected t q hq
  · exact fun dart next ↦
      norm_scaleColumns_le_of_norm_le_one
        ({selected, selected.symm} : Finset G.Dart) t
        (ons_kwAddedEdgeBaseMatrix G embedding weight)
        q ht hentry dart next
  · exact hsmall
  · exact hcard



theorem hasDerivAt_ons_kwAddedEdgeRoot_zero
    (embedding : KWStraightLineEmbedding G)
    (weight : Sym2 V → Complex) (selected : G.Dart)
    (q : Real) (hq : 0 ≤ q)
    (hentry : ∀ dart next,
      ‖ons_kwAddedEdgeBaseMatrix G embedding weight dart next‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card G.Dart : Real) ^ 2)⁻¹)
    (hcard : (Fintype.card G.Dart : Real) * q < 1) :
    HasDerivAt (ons_kwAddedEdgeRoot G embedding weight selected)
      (-(ons_kwAddedEdgeDeletedRoot G embedding weight selected *
        ons_kwAddedEdgeRootedSeries G embedding weight selected)) 0 := by
  let A := ons_kwAddedEdgeDeletedRoot G embedding weight selected
  let S := ons_kwAddedEdgeRootedSeries G embedding weight selected
  have haffine : HasDerivAt (fun t : Complex ↦ A * (1 - t * S))
      (-(A * S)) 0 := by
    convert ((hasDerivAt_const (x := (0 : Complex)) (1 : Complex)).sub
      ((hasDerivAt_id (x := (0 : Complex))).mul_const S)).const_mul A using 1
    · ring
  apply haffine.congr_of_eventuallyEq
  filter_upwards [Metric.ball_mem_nhds (0 : Complex) (by norm_num : (0 : Real) < 1)]
    with t ht
  rw [Metric.mem_ball, dist_zero_right] at ht
  exact ons_kwAddedEdgeRoot_eq_deleted_mul_rooted
    G embedding weight selected q hq hentry hsmall hcard t ht.le

end

end StatMech.Onsager
