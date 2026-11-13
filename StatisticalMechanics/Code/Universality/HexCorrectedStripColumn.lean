/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.Universality.HexCorrectedColumnLength
import Code.Universality.HexCorrectedStripFamilyMass
import Code.Universality.HexCorrectedStripIdentity

namespace StatMech.Universality

open HexWalk
open scoped BigOperators

noncomputable section


noncomputable def hexCSTopFiniteWeight
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ) : ℝ := by
  classical
  exact if HexCSTopWalk T L hT ts then
      hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices
    else 0

theorem hexCSTopFiniteWeight_nonneg
    (T L : ℕ) (hT : 0 < T) (ts : List ℤ) :
    0 ≤ hexCSTopFiniteWeight T L hT ts := by
  unfold hexCSTopFiniteWeight
  split
  · exact pow_nonneg (le_of_lt hexChiE_pos) _
  · exact le_rfl



theorem hexCSTopFiniteWeight_summable
    (T L : ℕ) (hT : 0 < T) :
    Summable (hexCSTopFiniteWeight T L hT) := by
  let S := (hexFinite_boundedLegal_finite
    (hexCSFiniteRegion T L hT).verts.card).toFinset
  apply summable_of_ne_finset_zero (s := S)
  intro ts hts
  by_contra hne
  apply hts
  change ts ∈ (hexFinite_boundedLegal_finite
    (hexCSFiniteRegion T L hT).verts.card).toFinset
  rw [Set.Finite.mem_toFinset]
  have hwalk : HexCSTopWalk T L hT ts := by
    by_contra hnwalk
    unfold hexCSTopFiniteWeight at hne
    rw [if_neg hnwalk] at hne
    exact hne rfl
  exact ⟨hwalk.1.1,
    (hexCSFiniteRegion T L hT).endpointLength_le
      hexAWStart 1 ts hwalk.1.2 hwalk.2.1⟩



theorem hexCSB_eq_topFiniteWeight_tsum
    (T L : ℕ) (hT : 0 < T) :
    hexCSB T L hT = ∑' ts, hexCSTopFiniteWeight T L hT ts := by
  rw [hexCSB_eq_classWalkMass]
  unfold hexCSClassWalkMass hexCSTopFiniteWeight
  apply tsum_congr
  intro ts
  by_cases hclass : HexCSClassWalk T L hT .top ts
  · have htop := (hexCSClassWalk_top_iff T L hT ts).mp hclass
    simp [hclass, htop]
  · have htop : ¬ HexCSTopWalk T L hT ts := fun h =>
      hclass ((hexCSClassWalk_top_iff T L hT ts).mpr h)
    simp [hclass, htop]


theorem hexCSB_le_one_of_exit_window
    (T L : ℕ) (hT : 0 < T)
    (hlocal : HexCSLocalRelation T L hT)
    (hwindow : HexCSBoundaryWindowLaw T L hT) :
    hexCSB T L hT ≤ 1 := by
  have hid := hexCS_finite_strip_identity_of_exit_window T L hT hlocal
    (hexCS_boundaryExitLaw T L hT) hwindow
  have hnn := hexCS_boundary_masses_nonneg_of_exit_window T L hT hlocal
    (hexCS_boundaryExitLaw T L hT) hwindow
  have hcl : 0 ≤ hexCl := le_of_lt hexCl_pos
  have hct : 0 ≤ hexCt := le_of_lt hexCt_pos
  nlinarith



theorem hexCSTopAtWidth_finset_bound
    (T : ℕ) (hT : 0 < T)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT)
    (s : Finset {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}) :
    ∑ w ∈ s,
        hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices ≤ 1 := by
  classical
  let L := hexCSTopFinsetHeight s
  let vals : Finset (List ℤ) := s.image Subtype.val
  have hvals :
      (∑ w ∈ s,
          hexChiE ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices) =
        ∑ ts ∈ vals,
          hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices := by
    unfold vals
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [hvals]
  calc
    (∑ ts ∈ vals,
        hexChiE ^ (ofTurns hexAWStart 1 ts).endpointNumVertices) =
        ∑ ts ∈ vals, hexCSTopFiniteWeight T L hT ts := by
      apply Finset.sum_congr rfl
      intro ts hts
      rw [Finset.mem_image] at hts
      obtain ⟨w, hw, rfl⟩ := hts
      rw [hexCSTopFiniteWeight, if_pos]
      exact hexCSTopWalk_finset_fits s w hw
    _ ≤ ∑' ts, hexCSTopFiniteWeight T L hT ts :=
      (hexCSTopFiniteWeight_summable T L hT).sum_le_tsum vals
        (fun ts _ => hexCSTopFiniteWeight_nonneg T L hT ts)
    _ = hexCSB T L hT := (hexCSB_eq_topFiniteWeight_tsum T L hT).symm
    _ ≤ 1 := hexCSB_le_one_of_exit_window T L hT
      (hlocal L) (hwindow L)




noncomputable def hexCSTopColumn
    (T : ℕ) (hT : 0 < T)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT) :
    HexColumn T hexChiE where
  W := {ts : List ℤ // HexCSTopWalkAtWidth T hT ts}
  len := fun w => (ofTurns hexAWStart 1 w.1).endpointNumVertices
  len_ge := fun w => hexCSTopWalkAtWidth_length_ge T hT w.1 w.2
  crit_summable := by
    apply summable_of_sum_le
    · intro w
      exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact hexCSTopAtWidth_finset_bound T hT hlocal hwindow
  crit_le_one := by
    apply Real.tsum_le_of_sum_le
    · intro w
      exact pow_nonneg (le_of_lt hexChiE_pos) _
    · exact hexCSTopAtWidth_finset_bound T hT hlocal hwindow

@[simp] theorem hexCSTopColumn_colSum
    (T : ℕ) (hT : 0 < T)
    (hlocal : ∀ L, HexCSLocalRelation T L hT)
    (hwindow : ∀ L, HexCSBoundaryWindowLaw T L hT)
    (x : ℝ) :
    (hexCSTopColumn T hT hlocal hwindow).colSum x =
      ∑' w : {ts : List ℤ // HexCSTopWalkAtWidth T hT ts},
        x ^ (ofTurns hexAWStart 1 w.1).endpointNumVertices := rfl

end

end StatMech.Universality
