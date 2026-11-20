/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Universality.HexCorrectedStripStartReturn
import Code.Universality.HexCorrectedStripLimits

namespace StatMech.Universality

open Complex HexWalk

noncomputable section



theorem hexCS_startReturnLaw (T L : ℕ) (hT : 0 < T) :
    HexCSStartReturnLaw T L hT := by
  intro ts hadm
  exact hexCS_endpoint_return_eq_nil T L hT ts hadm






def HexCSBoundaryExitLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt
          (hexAWMid e.vtx.1 e.edge) →
      hexInfra_midAccum hexAWStart 1 ts +
          halfStep (hexInfra_headAccum 1 ts) =
        hexAWMid e.vtx.1 e.edge +
          halfStep (hexCSCanonicalHeading e)





def HexCSBoundaryWindowLaw (T L : ℕ) (hT : 0 < T) : Prop :=
  ∀ (e : HexCSIncidence T L) (ts : List ℤ),
    e ∈ hexCSBoundaryIncidences T L →
    e ≠ hexCSStartIncidence T L hT →
    (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 ts).StaysIn
          (hexCSFiniteRegion T L hT).inRegion ∧
        (ofTurns hexAWStart 1 ts).EndsAt
          (hexAWMid e.vtx.1 e.edge) →
      ∃ w : ℤ,
        w ≤ hexInfra_headAccum 1 ts ∧
          hexInfra_headAccum 1 ts < w + 6 ∧
          w ≤ hexCSCanonicalHeading e ∧
          hexCSCanonicalHeading e < w + 6



theorem hexCSCanonicalWindingLaw_of_exit_window
    {T L : ℕ} {hT : 0 < T}
    (hexit : HexCSBoundaryExitLaw T L hT)
    (hwindow : HexCSBoundaryWindowLaw T L hT) :
    HexCSCanonicalWindingLaw T L hT := by
  intro e ts he hne hadm
  have hdvd : (6 : ℤ) ∣
      (hexInfra_headAccum 1 ts - hexCSCanonicalHeading e) := by
    apply hexInfra_finalHeading_mod_of_lastVertex hexAWStart 1
      (hexAWMid e.vtx.1 e.edge) (hexCSCanonicalHeading e) ts hadm.2.2
    exact hexit e ts he hne hadm
  obtain ⟨w, hwalkL, hwalkU, hedgeL, hedgeU⟩ :=
    hwindow e ts he hne hadm
  omega










theorem hexCS_finite_strip_identity_of_exit_window
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hexit : HexCSBoundaryExitLaw T L hT)
    (hwindow : HexCSBoundaryWindowLaw T L hT) :
    hexCl * hexCSA T L hT + hexCt * hexCSE T L hT +
      hexCSB T L hT = 1 := by
  exact hexCS_finite_strip_identity T L hT hlocal
    (hexCSCanonicalWindingLaw_of_exit_window hexit hwindow)
    (hexCS_startReturnLaw T L hT)

theorem hexCS_boundary_masses_nonneg_of_exit_window
    (T L : ℕ) (hT : 0 < T) (hlocal : HexCSLocalRelation T L hT)
    (hexit : HexCSBoundaryExitLaw T L hT)
    (hwindow : HexCSBoundaryWindowLaw T L hT) :
    0 ≤ hexCSA T L hT ∧ 0 ≤ hexCSE T L hT ∧
      0 ≤ hexCSB T L hT := by
  exact hexCS_boundary_masses_nonneg T L hT hlocal
    (hexCSCanonicalWindingLaw_of_exit_window hexit hwindow)
    (hexCS_startReturnLaw T L hT)

end

end StatMech.Universality
