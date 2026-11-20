/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Universality.HexEndpointCyclicLocalPartition

namespace StatMech.Universality

open Complex HexWalk

noncomputable section



theorem endpointCombinedSummand_ne_zero_of_valid_at_label
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (j : Fin 3) {ts : List ℤ}
    (hvalid : (ofTurns a h0 ts).EndpointIsLegalSAW ∧
      (ofTurns a h0 ts).StaysIn region ∧
      (ofTurns a h0 ts).EndsAt (labelMid v du j)) :
    endpointCombinedSummand region a h0 v du ts ≠ 0 := by
  rw [endpointCombinedSummand_at_label hdu j hvalid.2.2]
  apply mul_ne_zero
  · have hω : hexOmega ≠ 0 :=
      hexOmega_primRoot.ne_zero (by norm_num)
    fin_cases j <;> simp [labelMid, hdu, hω]
  · unfold endpointParafSummand
    rw [if_pos hvalid]
    apply mul_ne_zero (Complex.exp_ne_zero _)
    exact pow_ne_zero _
      (Complex.ofReal_ne_zero.mpr (ne_of_gt hexChi_pos))



theorem HexEndpointCyclicTriplet.piece_subset_endpointCombinedSupportFinset
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0)
    (C : HexEndpointCyclicTriplet R.inRegion a h0 v du) :
    C.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
  intro ts hts
  rw [R.mem_endpointCombinedSupportFinset]
  simp only [HexEndpointCyclicTriplet.piece, Finset.mem_insert,
    Finset.mem_singleton] at hts
  rcases hts with rfl | rfl | rfl
  · exact endpointCombinedSummand_ne_zero_of_valid_at_label
      hdu C.baseLabel C.base_valid
  · exact endpointCombinedSummand_ne_zero_of_valid_at_label
      hdu (hexCyclicSucc C.baseLabel) C.succ_valid
  · exact endpointCombinedSummand_ne_zero_of_valid_at_label
      hdu (hexCyclicPred C.baseLabel) C.pred_valid



theorem HexEndpointCyclicLoopPair.piece_subset_endpointCombinedSupportFinset
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0)
    (P : HexEndpointCyclicLoopPair R.inRegion a h0 v du) :
    P.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
  intro ts hts
  rw [R.mem_endpointCombinedSupportFinset]
  simp only [HexEndpointCyclicLoopPair.piece, Finset.mem_insert,
    Finset.mem_singleton] at hts
  rcases hts with rfl | rfl
  · exact endpointCombinedSummand_ne_zero_of_valid_at_label
      hdu (hexCyclicSucc P.baseLabel) P.succ_valid
  · exact endpointCombinedSummand_ne_zero_of_valid_at_label
      hdu (hexCyclicPred P.baseLabel) P.pred_valid


theorem HexEndpointCyclicLocalAtom.piece_subset_endpointCombinedSupportFinset
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0)
    (A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du) :
    A.piece ⊆ R.endpointCombinedSupportFinset a h0 v du := by
  cases A with
  | triplet C => exact C.piece_subset_endpointCombinedSupportFinset hdu
  | pair P => exact P.piece_subset_endpointCombinedSupportFinset hdu


theorem HexEndpointCyclicLocalAtom.mem_endpointCombinedSupportFinset_of_mem_piece
    {R : HexFiniteRegion} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0)
    (A : HexEndpointCyclicLocalAtom R.inRegion a h0 v du)
    {ts : List ℤ} (hts : ts ∈ A.piece) :
    ts ∈ R.endpointCombinedSupportFinset a h0 v du :=
  A.piece_subset_endpointCombinedSupportFinset hdu hts

end

end StatMech.Universality
