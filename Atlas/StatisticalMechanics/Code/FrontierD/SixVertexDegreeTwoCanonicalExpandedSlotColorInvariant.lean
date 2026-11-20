/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoAlignedSlotColorInvariant











namespace StatMech.FrontierD

noncomputable section

local instance canonicalExpandedActiveDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _



noncomputable def sixVertexDegreeTwoCanonicalTransitionMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex) : Bool := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · exact false
  · by_cases hright : cut.cutRight = []
    · exact false
    · exact decide (v = doubledAlignedVertex (cut.cutRight.head hright)) ||
        decide (v = doubledAlignedVertex (cut.cutLeft.head hleft))

theorem fkMedialTogglePairingAt_two_eq_toggleMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) (hne : first ≠ second) :
    fkMedialTogglePairingAt (fkMedialTogglePairingAt pairing first) second =
      fkMedialTogglePairingMask pairing
        (fun v => decide (v = first) || decide (v = second)) := by
  funext v
  by_cases hfirst : v = first <;> by_cases hsecond : v = second
  · exact False.elim (hne (hfirst.symm.trans hsecond))
  all_goals simp [fkMedialTogglePairingAt, fkMedialTogglePairingMask,
    hfirst, hsecond, hne, Ne.symm hne]

theorem sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      fkMedialTogglePairingMask
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · rw [sixVertexDegreeTwoAlignedTargetPairing_of_left_empty homega heta
      hdegree middle homegaSector hetaSector hmiddle hleft]
    funext v
    simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft,
      fkMedialTogglePairingMask]
  · by_cases hright : cut.cutRight = []
    · rw [sixVertexDegreeTwoAlignedTargetPairing_of_right_empty homega heta
        hdegree middle homegaSector hetaSector hmiddle hright]
      funext v
      simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
        fkMedialTogglePairingMask]
    · rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper homega heta
        hdegree middle homegaSector hetaSector hmiddle hleft hright]
      by_cases hvertices : doubledAlignedVertex (cut.cutRight.head hright) =
          doubledAlignedVertex (cut.cutLeft.head hleft)
      · rw [sixVertexRetieAtTransitionVertices_of_eq _ hvertices]
        funext v
        simp [
          sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
          fkMedialTogglePairingMask, fkMedialTogglePairingAt, hvertices]
      · rw [sixVertexRetieAtTransitionVertices_of_ne _ hvertices]
        rw [fkMedialTogglePairingAt_two_eq_toggleMask _ _ _ hvertices]
        funext v
        simp [
          sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft, hright,
          fkMedialTogglePairingMask, hvertices]

@[simp] theorem fkMedialTogglePairingMask_compose
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex -> Bool) :
    fkMedialTogglePairingMask (fkMedialTogglePairingMask pairing first)
        second =
      fkMedialTogglePairingMask pairing (fun v => first v != second v) := by
  funext v
  cases hfirst : first v <;> cases hsecond : second v <;>
    simp [fkMedialTogglePairingMask, hfirst, hsecond]


noncomputable def sixVertexDegreeTwoCanonicalSelectedVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    decide ((d, false) ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta
        hdegree middle homegaSector hetaSector hmiddle) ||
      decide ((d, true) ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta
        hdegree middle homegaSector hetaSector hmiddle)
  else false





noncomputable def sixVertexDegreeTwoCanonicalInternalMismatchVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (transition && !selected) ||
      (selected &&
        ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ))
  else false



noncomputable def sixVertexDegreeTwoCanonicalCorrectionMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (_layer : Bool) (v : T.Vertex) : Bool :=
  sixVertexDegreeTwoCanonicalInternalMismatchVertex homega heta hdegree
    middle homegaSector hetaSector hmiddle v


noncomputable def sixVertexDegreeTwoCanonicalExpandedTargetPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) : FKMedialLoopPairing T :=
  fkMedialTogglePairingMask
    (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
      homegaSector hetaSector hmiddle layer)
    (sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer)

theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      fkMedialTogglePairingMask
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (fun v => sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree
            middle homegaSector hetaSector hmiddle v !=
          sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
            homegaSector hetaSector hmiddle layer v) := by
  rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing,
    sixVertexDegreeTwoAlignedTargetPairing_eq_toggleMask,
    fkMedialTogglePairingMask_compose]

theorem sixVertexDegreeTwoCanonicalCorrectionMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer v =
      ((transition && !selected) ||
        (selected &&
          ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) := by
  simp [sixVertexDegreeTwoCanonicalCorrectionMask,
    sixVertexDegreeTwoCanonicalInternalMismatchVertex, hactive]



@[simp] theorem sixVertexDegreeTwoCanonicalCorrectionMask_layer_independent
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (first second : Bool) (v : T.Vertex) :
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle first v =
      sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle second v := by
  rfl




theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (if selected then
          if transition then !retie.pairingQ else retie.pairingQ
        else retie.pairingP,
        if selected then
          if transition then !retie.pairingP else retie.pairingP
        else retie.pairingQ) := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  have hfalse := congrFun
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask homega heta
      hdegree middle homegaSector hetaSector hmiddle false) v
  have htrue := congrFun
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask homega heta
      hdegree middle homegaSector hetaSector hmiddle true) v
  have hP := alignedRoutingPairing_eq_at_active homega heta hdegree false v
    hactive
  have hQ := alignedRoutingPairing_eq_at_active homega heta hdegree true v
    hactive
  change alignedRoutingLoopPairing homega heta hdegree false v =
    retie.pairingP at hP
  change alignedRoutingLoopPairing homega heta hdegree true v =
    retie.pairingQ at hQ
  have hcorrectionFalse := sixVertexDegreeTwoCanonicalCorrectionMask_active
    homega heta hdegree middle homegaSector hetaSector hmiddle false v hactive
  have hcorrectionTrue := sixVertexDegreeTwoCanonicalCorrectionMask_active
    homega heta hdegree middle homegaSector hetaSector hmiddle true v hactive
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle false v =
    ((transition && !selected) ||
      (selected && (retie.pairingP != retie.pairingQ))) at hcorrectionFalse
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle true v =
    ((transition && !selected) ||
      (selected && (retie.pairingP != retie.pairingQ))) at hcorrectionTrue
  change sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle false v =
    (if transition !=
        sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle false v then
      !alignedRoutingLoopPairing homega heta hdegree false v
    else alignedRoutingLoopPairing homega heta hdegree false v) at hfalse
  change sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle true v =
    (if transition !=
        sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle true v then
      !alignedRoutingLoopPairing homega heta hdegree true v
    else alignedRoutingLoopPairing homega heta hdegree true v) at htrue
  rw [hP, hcorrectionFalse] at hfalse
  rw [hQ, hcorrectionTrue] at htrue
  change (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle false v,
    sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle true v) =
    (if selected then
        if transition then !retie.pairingQ else retie.pairingQ
      else retie.pairingP,
      if selected then
        if transition then !retie.pairingP else retie.pairingP
      else retie.pairingQ)
  rw [hfalse, htrue]
  cases transition <;> cases selected <;> cases retie.pairingP <;>
    cases retie.pairingQ <;> decide




theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_emptyCut_regression
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2)
    (hempty :
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutLeft = [] \/
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutRight = [])
    (hselected : sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree
      middle homegaSector hetaSector hmiddle v = true)
    (hmismatch :
      let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
      (orientedDartAlignedRetie homega heta hdegree d).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ = true) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (retie.pairingQ, retie.pairingP) /\
    (retie.pairingP != retie.pairingQ) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  have htransition : sixVertexDegreeTwoCanonicalTransitionMask homega heta
      hdegree middle homegaSector hetaSector hmiddle v = false := by
    rcases hempty with hleft | hright
    · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft]
    · by_cases hleft : cut.cutLeft = []
      · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft]
      · simp [sixVertexDegreeTwoCanonicalTransitionMask, cut, hleft,
          hright]
  have htable := sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    homega heta hdegree middle homegaSector hetaSector hmiddle v hactive
  change (_, _) =
    (if sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v then
      if sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle v then !retie.pairingQ
      else retie.pairingQ
    else retie.pairingP,
    if sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v then
      if sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle v then !retie.pairingP
      else retie.pairingP
    else retie.pairingQ) at htable
  constructor
  · simpa [htransition, hselected] using htable
  · exact hmismatch

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkMedialTogglePairingMask
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
          homegaSector hetaSector hmiddle layer) =
      sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer := by
  exact fkMedialTogglePairingMask_self _ _


noncomputable def sixVertexDegreeTwoCanonicalExpandedRetieMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex) : Bool :=
  sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v !=
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v

theorem sixVertexDegreeTwoCanonicalExpandedTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) =
      (fkColoredParityMaskStrandSlotSwap
        (sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
        (fkColoredParityMaskStrandSlotSwap
          (sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
            middle homegaSector hetaSector hmiddle layer) true)) := by
  rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask]
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _


noncomputable def sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) : FKMedialBlackDart T :=
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  let input := sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
    mask false layer dart
  let arrival := alignedBoundaryPerm homega heta hdegree false input
  let common := if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm arrival
    else arrival
  sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask true
    layer common

theorem sixVertexDegreeTwoCanonicalExpandedTargetBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
          hdegree middle homegaSector hetaSector hmiddle layer dart) := by
  rw [sixVertexDegreeTwoCanonicalExpandedTargetBoundary]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl

theorem sixVertexDegreeTwoCanonicalExpandedSlotColorInvariant_of_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hfalseDart : forall (layer : Bool) (dart : FKMedialBlackDart T),
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (fkIndexedOccurrenceSlotEquiv
            (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
              heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
              homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta
              hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
                hdegree middle homegaSector hetaSector hmiddle layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (fkIndexedOccurrenceSlotEquiv
            (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
              heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
              homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta
              hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
        middle homegaSector hetaSector hmiddle) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot homega heta hdegree
    layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  rw [← hslot, fkColoredLayeredStrandSlotBoundaryPerm_apply,
    sixVertexDegreeTwoCanonicalExpandedTargetBoundary_slotOfFalseDart]
  exact hfalseDart layer dart



noncomputable def sixVertexDegreeTwoCanonicalExpandedRecoverPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) : FKMedialLoopPairing T := by
  let corrected := fkMedialTogglePairingMask
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
      middle homegaSector hetaSector hmiddle layer)
    (sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer)
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · exact corrected
  · by_cases hright : cut.cutRight = []
    · exact corrected
    · exact sixVertexRetieAtTransitionVertices corrected
        (doubledAlignedVertex (cut.cutRight.head hright))
        (doubledAlignedVertex (cut.cutLeft.head hleft))

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedRecoverPairing_eq_source
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    sixVertexDegreeTwoCanonicalExpandedRecoverPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · simp [sixVertexDegreeTwoCanonicalExpandedRecoverPairing, cut, hleft,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover,
      sixVertexDegreeTwoAlignedTargetPairing_of_left_empty]
  · by_cases hright : cut.cutRight = []
    · simp [sixVertexDegreeTwoCanonicalExpandedRecoverPairing, cut, hleft,
        hright, sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover,
        sixVertexDegreeTwoAlignedTargetPairing_of_right_empty]
    · rw [sixVertexDegreeTwoCanonicalExpandedRecoverPairing]
      simp only [cut, hleft, hright, dite_false]
      rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing_recover]
      exact sixVertexDegreeTwoAlignedTargetPairing_recover_of_proper homega
        heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer

end

end StatMech.FrontierD
