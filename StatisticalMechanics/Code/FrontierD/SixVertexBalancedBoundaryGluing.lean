/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexRectangleGluing
import Code.FrontierD.SixVertexRectangleTorusCut

open Finset

namespace StatMech.FrontierD


def EvenTorus.double (T : EvenTorus) : EvenTorus where
  width := T.width + T.width
  height := T.height + T.height
  width_pos := Nat.add_pos_left T.width_pos T.width
  height_pos := Nat.add_pos_left T.height_pos T.height
  width_even := T.width_even.add T.width_even
  height_even := T.height_even.add T.height_even



theorem sixVertexDoubledToroidalBoundary_balanced {N M : ℕ}
    (xi : SixVertexToroidalBoundary N M) :
    (sixVertexDoubledToroidalBoundary xi).Balanced := by
  unfold SixVertexToroidalBoundary.Balanced
  rw [Finset.card_filter, Fin.sum_univ_add]
  simp only [sixVertexDoubledToroidalBoundary, Fin.addCases_left,
    Fin.addCases_right]
  rw [show (N + N) / 2 = N by omega]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun i : Fin N => xi.2 i = true)
  rw [Finset.card_filter, Finset.card_filter] at hsplit
  simp only [Bool.not_eq_true] at hsplit
  have hrev :
      (∑ i : Fin N, if (!xi.2 i.rev : Bool) = true then 1 else 0) =
        ∑ i : Fin N, if xi.2 i = false then 1 else 0 := by
    apply Fintype.sum_equiv Fin.revPerm
    intro i
    simp
  rw [hrev]
  simpa using hsplit



theorem sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBalanced
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : Real} (hc : 0 <= c) (xi : SixVertexToroidalBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexToroidalRectangleBoundary xi) ^ 4 <=
      sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c := by
  refine (sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBoundary
    hN hM hc xi).trans ?_
  unfold sixVertexRectangleBalancedPartitionSum
  let f : SixVertexToroidalBoundary (N + N) (M + M) -> Real := fun eta =>
    if eta.Balanced then
      sixVertexRectangleBoundaryPartitionSum (N + N) (M + M) c
        (sixVertexToroidalRectangleBoundary eta)
    else 0
  have hsingle : f (sixVertexDoubledToroidalBoundary xi) <=
      ∑ eta ∈ Finset.univ, f eta := Finset.single_le_sum
    (f := f) (fun eta (_ : eta ∈ Finset.univ) => by
      dsimp [f]
      split_ifs
      · exact sixVertexRectangleBoundaryPartitionSum_nonneg
          (N + N) (M + M) hc _
      · exact le_rfl)
    (Finset.mem_univ (sixVertexDoubledToroidalBoundary xi))
  simpa [f, sixVertexDoubledToroidalBoundary_balanced] using hsingle



theorem
    sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubledBalanced
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {c : Real} (hc : 0 <= c) :
    sixVertexRectangleMaxToroidalBoundaryPartitionSum N M c ^ 4 <=
      sixVertexRectangleBalancedPartitionSum (N + N) (M + M) c := by
  obtain ⟨xi, hxi⟩ :=
    sixVertexRectangleMaxToroidalBoundary_exists N M c
  rw [← hxi]
  exact sixVertexRectangleBoundaryPartitionSum_pow_four_le_doubledBalanced
    hN hM hc xi





theorem sixVertexTorusArrowPartition_boundaryControl
    (T : EvenTorus) {c : Real} (hc : 0 <= c) :
    sixVertexTorusArrowPartitionSum T c <=
        (2 : Real) ^ (T.width + T.height) *
          sixVertexRectangleMaxToroidalBoundaryPartitionSum
            T.width T.height c ∧
      sixVertexRectangleMaxToroidalBoundaryPartitionSum
          T.width T.height c ^ 4 <=
        sixVertexTorusArrowPartitionSum T.double c := by
  constructor
  · exact sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary T c
  · rw [← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
    exact
      sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubled
        T.width_pos T.height_pos hc



theorem sixVertexTorusArrowPartitionSum_pow_four_le_boundaryFactor_mul_balanced
    (T : EvenTorus) {c : Real} (hc : 0 <= c) :
    sixVertexTorusArrowPartitionSum T c ^ 4 <=
      (2 : Real) ^ (4 * (T.width + T.height)) *
        sixVertexRectangleBalancedPartitionSum
          (T.width + T.width) (T.height + T.height) c := by
  let Z := sixVertexTorusArrowPartitionSum T c
  let K := sixVertexRectangleMaxToroidalBoundaryPartitionSum
    T.width T.height c
  let B := sixVertexRectangleBalancedPartitionSum
    (T.width + T.width) (T.height + T.height) c
  have hZ : 0 <= Z := by
    dsimp [Z]
    rw [← sixVertexRectangleToroidalPartitionSum_eq_torusArrowPartitionSum]
    exact sixVertexRectangleToroidalPartitionSum_nonneg _ _ hc
  have hZK : Z <= (2 : Real) ^ (T.width + T.height) * K :=
    sixVertexTorusArrowPartitionSum_le_card_mul_maxBoundary T c
  have hK : K ^ 4 <= B :=
    sixVertexRectangleMaxToroidalBoundaryPartitionSum_pow_four_le_doubledBalanced
      T.width_pos T.height_pos hc
  calc
    Z ^ 4 <= ((2 : Real) ^ (T.width + T.height) * K) ^ 4 :=
      pow_le_pow_left₀ hZ hZK 4
    _ = ((2 : Real) ^ (T.width + T.height)) ^ 4 * K ^ 4 := by
      rw [mul_pow]
    _ <= ((2 : Real) ^ (T.width + T.height)) ^ 4 * B :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    _ = (2 : Real) ^ (4 * (T.width + T.height)) * B := by
      rw [← pow_mul]
      congr 2
      omega




theorem sixVertexTorusArrowPartition_balancedBoundaryControl
    (T : EvenTorus) {c : Real} (hc : 0 <= c) :
    sixVertexRectangleBalancedPartitionSum
        (T.width + T.width) (T.height + T.height) c <=
        sixVertexTorusArrowPartitionSum T.double c ∧
      sixVertexTorusArrowPartitionSum T c ^ 4 <=
        (2 : Real) ^ (4 * (T.width + T.height)) *
          sixVertexRectangleBalancedPartitionSum
            (T.width + T.width) (T.height + T.height) c := by
  constructor
  · exact sixVertexRectangleBalancedPartitionSum_le_torusArrowPartitionSum
      T.double hc
  · exact
      sixVertexTorusArrowPartitionSum_pow_four_le_boundaryFactor_mul_balanced
        T hc

end StatMech.FrontierD
