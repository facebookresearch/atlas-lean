/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Universality.HexCorrectedHighestCut
import Code.Universality.HexLiteralHWColumns

namespace StatMech.Universality

open HexWalk

noncomputable section

private theorem hexCSTopOne_legal :
    (ofTurns hexAWStart 1 [1, -1]).IsLegalSAW := by
  constructor
  · simp [HexWalk.LegalTurns]
  · simp [HexWalk.IsSAW, HexWalk.vertices, HexWalk.ofTurns,
      HexWalk.verticesAux]
    constructor
    · constructor
      · intro h
        have hz : (2 : ℂ) * halfStep 2 = 0 := by
          linear_combination -h
        exact (mul_ne_zero (by norm_num) (hexConcrete_halfStep_ne 2)) hz
      · intro h
        have hz : halfStep 1 + halfStep 2 = 0 := by
          linear_combination (-1 / 2 : ℂ) * h
        exact hexW1_halfStep_add_ne_zero 1 1 (Or.inl rfl) hz
    · intro h
      have hz : (2 : ℂ) * halfStep 1 = 0 := by
        linear_combination -h
      exact (mul_ne_zero (by norm_num) (hexConcrete_halfStep_ne 1)) hz

private theorem hexCSTopOne_prefix_zero :
    hlhc_prefixCoord [1, -1] hexCSTopOne_legal.1 0 =
      hexAWOriginCoord := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex [1, -1] hexCSTopOne_legal.1 0]
  simp only [List.take_zero, hexInfra_midAccum_nil,
    hexInfra_headAccum_nil, hexAWPos_origin]
  unfold hexAWStart halfStep
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

private theorem hexCSTopOne_prefix_one :
    hlhc_prefixCoord [1, -1] hexCSTopOne_legal.1 1 =
      ⟨0, -1, .white⟩ := by
  apply hexAWPos_injective
  rw [← hlhc_prefixCoord_vertex [1, -1] hexCSTopOne_legal.1 1]
  simp only [List.take, hexInfra_midAccum_cons, hexInfra_midAccum_nil,
    hexInfra_headAccum_cons, hexInfra_headAccum_nil]
  unfold hexAWStart hexAWPos hexAWBasisJ hexAWAxis halfStep
  rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
  ring

private noncomputable def hexCSTopOneData :
    HLHCCanonicalColumnWalk 1 [1, -1] where
  legal := hexCSTopOne_legal
  horizontal := by
    intro k hk
    norm_num at hk
    interval_cases k
    · rw [hexCSTopOne_prefix_zero]
      norm_num [hexAWBookRe2, hexAWDepth, hexAWLong,
        hexAWOriginCoord]
    · rw [hexCSTopOne_prefix_one]
      norm_num [hexAWBookRe2, hexAWDepth, hexAWLong]
  topCoord := ⟨0, -1, .white⟩
  top_white := rfl
  top_depth := by
    norm_num [hexAWDepth, hexAWLong]
  endsAt := by
    rw [HexWalk.EndsAt, hexInfra_endMid_eq_midAccum]
    simp only [hexInfra_midAccum_cons, hexInfra_midAccum_nil]
    unfold hexAWMid hexAWPos hexAWNeighbor hexAWBasisJ hexAWAxis
      hexAWStart halfStep
    rw [show (4 : ℤ) = 1 + 3 by norm_num, hexUnit_add_three]
    ring



theorem hexCSTopWalkAtWidth_one_nonempty :
    ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts := by
  exact ⟨[1, -1], hexCSTopOneData.mem_topAtWidth (by norm_num)⟩



theorem hexCS_critical_divergence_of_recurrence_concrete
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) →
      ∀ T, 1 ≤ T →
        hexCSInfiniteSideMassAtWidth (T + 1) -
            hexCSInfiniteSideMassAtWidth T ≤
          hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) :=
  hexCS_critical_divergence_of_recurrence hlocal hwindow hrec
    hexCSTopWalkAtWidth_one_nonempty



theorem hexCS_critical_divergence_of_highestCuts
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
    (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
    (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) :=
  hexCS_critical_divergence_of_recurrence_concrete hlocal hwindow
    (hexCS_highestCuts_recurrence HC)

end

end StatMech.Universality
