/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedInactive

namespace StatMech.FrontierD

noncomputable section

local instance canonicalExpandedActiveActiveDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _


noncomputable def sixVertexDegreeTwoCanonicalSelected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) : Bool :=
  decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
    middle homegaSector hetaSector hmiddle)

theorem sixVertexDegreeTwoCanonicalSelected_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle (cut.cutRight.head hright) = false ∧
      sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle
        ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutRight.head hright)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have h := cut.rightHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright
  simpa [sixVertexDegreeTwoCanonicalSelected, h.1, h.2]

theorem sixVertexDegreeTwoCanonicalSelected_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle (cut.cutLeft.head hleft) = true ∧
      sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle homegaSector
        hetaSector hmiddle
        ((doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutLeft.head hleft)) = false := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have h := cut.leftHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright
  simpa [sixVertexDegreeTwoCanonicalSelected, h.1, h.2]

@[simp] theorem sixVertexDegreeTwoCanonicalTransitionMask_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutRight.head hright)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  simp [sixVertexDegreeTwoCanonicalTransitionMask, hleft, hright]

@[simp] theorem sixVertexDegreeTwoCanonicalTransitionMask_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutLeft.head hleft)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  simp [sixVertexDegreeTwoCanonicalTransitionMask, hleft, hright]

theorem sixVertexDegreeTwoCanonicalTransitionMask_proper
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (v : T.Vertex) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle v =
      (decide (v = doubledAlignedVertex (cut.cutRight.head hright)) ||
        decide (v = doubledAlignedVertex (cut.cutLeft.head hleft))) := by
  simp [sixVertexDegreeTwoCanonicalTransitionMask, hleft, hright]

theorem sixVertexDegreeTwoCanonicalSelectedVertex_of_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedVertex x) = true := by
  rcases x with ⟨dx, branch⟩
  let v := doubledAlignedVertex (dx, branch)
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree dx.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = dx := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d dx rfl
  unfold sixVertexDegreeTwoCanonicalSelectedVertex
  rw [dif_pos hactive]
  dsimp only
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = dx
    at hd
  rw [hd]
  cases branch <;> simp_all

theorem sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedVertex x) =
      (decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle) ||
        decide (doubledAlignedBranchSwap x ∈
          SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle)) := by
  rcases x with ⟨dx, branch⟩
  let v := doubledAlignedVertex (dx, branch)
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree dx.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = dx := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d dx rfl
  unfold sixVertexDegreeTwoCanonicalSelectedVertex
  rw [dif_pos hactive]
  dsimp only
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = dx at hd
  rw [hd]
  cases branch <;> simp [doubledAlignedBranchSwap, Bool.or_comm]

theorem sixVertexDegreeTwoCanonicalSelectedVertex_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedVertex x) = true ↔
      x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle ∨
        doubledAlignedBranchSwap x ∈
          SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle := by
  rw [sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership]
  simp

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex x) =
      let transition := sixVertexDegreeTwoCanonicalTransitionMask homega heta
        hdegree middle homegaSector hetaSector hmiddle (doubledAlignedVertex x)
      let selected :=
        (decide (x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta
            hdegree middle homegaSector hetaSector hmiddle) ||
          decide (doubledAlignedBranchSwap x ∈
            SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
              homegaSector hetaSector hmiddle))
      transition != ((transition && !selected) ||
        (selected &&
          ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
            (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  unfold sixVertexDegreeTwoCanonicalExpandedRetieMask
  rw [sixVertexDegreeTwoCanonicalCorrectionMask_active homega heta hdegree
      middle homegaSector hetaSector hmiddle layer v hactive,
    sixVertexDegreeTwoCanonicalSelectedVertex_eq_membership]
  change orientedDisagreementDartAtActiveVertex homega heta v hactive = x.1 at hd
  rw [hd]

@[simp] theorem sixVertexDegreeTwoCanonicalSelectedVertex_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutLeft.head hleft)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have hmem := (cut.leftHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright).1
  exact sixVertexDegreeTwoCanonicalSelectedVertex_of_mem homega heta hdegree
    middle homegaSector hetaSector hmiddle (cut.cutLeft.head hleft) hmem

@[simp] theorem sixVertexDegreeTwoCanonicalSelectedVertex_rightHead_of_coincident
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedVertex (cut.cutRight.head hright)) = true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  change sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
      homegaSector hetaSector hmiddle
      (doubledAlignedVertex (cut.cutRight.head hright)) = true
  change doubledAlignedVertex (cut.cutRight.head hright) =
      doubledAlignedVertex (cut.cutLeft.head hleft) at hvertex
  rw [hvertex]
  exact sixVertexDegreeTwoCanonicalSelectedVertex_leftHead homega heta hdegree
    middle homegaSector hetaSector hmiddle hleft hright

theorem sixVertexDegreeTwoCanonicalCorrectionMask_of_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex x) =
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) := by
  let v := doubledAlignedVertex x
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree x.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = x.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d x.1 rfl
  have hcorrection := sixVertexDegreeTwoCanonicalCorrectionMask_active homega
    heta hdegree middle homegaSector hetaSector hmiddle layer v hactive
  have hselected := sixVertexDegreeTwoCanonicalSelectedVertex_of_mem homega
    heta hdegree middle homegaSector hetaSector hmiddle x hx
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v =
    ((sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
      !sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v) ||
      (sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
        ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) at hcorrection
  rw [hselected, hd] at hcorrection
  simpa using hcorrection

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let left := cut.cutLeft.head hleft
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex left) =
      !((orientedDartAlignedRetie homega heta hdegree left.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let left := cut.cutLeft.head hleft
  have hmem := (cut.leftHead_transition homega heta hdegree middle homegaSector
    hetaSector hmiddle hleft hright).1
  change (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle (doubledAlignedVertex left) !=
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer (doubledAlignedVertex left)) = _
  rw [sixVertexDegreeTwoCanonicalTransitionMask_leftHead homega heta hdegree
      middle homegaSector hetaSector hmiddle hleft hright,
    sixVertexDegreeTwoCanonicalCorrectionMask_of_mem homega heta hdegree
      middle homegaSector hetaSector hmiddle layer left hmem]
  cases (orientedDartAlignedRetie homega heta hdegree left.1).pairingP <;>
    cases (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ <;>
    decide

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle
        (doubledAlignedVertex right)
    let mismatch :=
      (orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) =
      (selected && !mismatch) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let v := doubledAlignedVertex right
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree right.1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd : d = right.1 := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d right.1 rfl
  have htransition := sixVertexDegreeTwoCanonicalTransitionMask_rightHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hcorrection := sixVertexDegreeTwoCanonicalCorrectionMask_active homega
    heta hdegree middle homegaSector hetaSector hmiddle layer v hactive
  change sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v = true at htransition
  change sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v =
    ((sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
      !sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v) ||
      (sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle v &&
        ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ))) at hcorrection
  change (sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v !=
    sixVertexDegreeTwoCanonicalCorrectionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v) = _
  rw [htransition] at hcorrection
  rw [htransition, hcorrection, hd]
  cases sixVertexDegreeTwoCanonicalSelectedVertex homega heta hdegree middle
      homegaSector hetaSector hmiddle v <;>
    cases (orientedDartAlignedRetie homega heta hdegree right.1).pairingP <;>
    cases (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ <;>
    decide

theorem sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) =
      !((orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  have hbranch :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
      hvertex
  have hleftMask := sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright layer
  change sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer (doubledAlignedVertex right) = _
  change (cut.cutLeft.head hleft) = doubledAlignedBranchSwap right at hbranch
  have hfirst : (cut.cutLeft.head hleft).1 = right.1 := by
    simpa [doubledAlignedBranchSwap] using congrArg
      (fun z : DoubledAlignedState omega eta => z.1) hbranch
  dsimp only at hleftMask
  rw [hfirst] at hleftMask
  rw [hvertex]
  exact hleftMask



theorem sixVertexDegreeTwoCanonicalTransportedColor_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
            homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
          homegaSector hetaSector hmiddle x then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  rw [sixVertexDegreeTwoAlignedTransportedColor_active]
  by_cases hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta
      hdegree middle homegaSector hetaSector hmiddle
  · simp [sixVertexDegreeTwoCanonicalSelected, hx]
  · simp [sixVertexDegreeTwoCanonicalSelected, hx]

noncomputable def sixVertexDegreeTwoCanonicalTransportedActiveColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) : Bool :=
  fkColoredLayeredSlotColor
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (fkIndexedOccurrenceSlotEquiv
      (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (layer, doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))

def sixVertexDegreeTwoAlignedActiveColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) : Bool :=
  fkColoredLayeredSlotColor
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (layer, doubledAlignedVertex x,
      doubledAlignedSlot homega heta hdegree layer x)

theorem sixVertexDegreeTwoAlignedActiveColor_false_branchSwap_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        (doubledAlignedBranchSwap x)) =
      (sixVertexLocalIncomingPattern omega (doubledAlignedVertex x) 0 !=
        sixVertexLocalIncomingPattern omega (doubledAlignedVertex x) 1) := by
  rw [sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  rcases x with ⟨d, branch⟩
  simp only [doubledAlignedVertex, doubledAlignedBranchSwap,
    doubledAlignedSlot]
  cases branch <;>
    cases hp : fkMedialVertexParity d.1.1.1 <;>
    cases hs : orientedDartBoundaryAlignedSlot homega heta hdegree false d <;>
    simp [horizontalSlot, bne_comm]

theorem sixVertexDegreeTwoAlignedActiveColor_true_branchSwap_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap x)) =
      (sixVertexLocalIncomingPattern eta (doubledAlignedVertex x) 0 !=
        sixVertexLocalIncomingPattern eta (doubledAlignedVertex x) 1) := by
  rw [sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedActiveColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  rcases x with ⟨d, branch⟩
  simp only [doubledAlignedVertex, doubledAlignedBranchSwap,
    doubledAlignedSlot]
  cases branch <;>
    cases hp : fkMedialVertexParity d.1.1.1 <;>
    cases hs : orientedDartBoundaryAlignedSlot homega heta hdegree true d <;>
    simp [horizontalSlot, bne_comm]

theorem sixVertexDegreeTwoCanonicalTransportedColor_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutRight.head hright
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer head =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer head ∧
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer predecessor =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer)
        predecessor := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutRight.head hright
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have hselected := sixVertexDegreeTwoCanonicalSelected_rightHead homega heta
    hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle head = false ∧
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle predecessor = true at hselected
  constructor
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.1]
    rfl
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.2]
    rfl

theorem sixVertexDegreeTwoCanonicalTransportedColor_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutLeft.head hleft
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer head =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) head ∧
    sixVertexDegreeTwoCanonicalTransportedActiveColor homega heta hdegree
        middle homegaSector hetaSector hmiddle layer predecessor =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer
        predecessor := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutLeft.head hleft
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have hselected := sixVertexDegreeTwoCanonicalSelected_leftHead homega heta
    hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle head = true ∧
    sixVertexDegreeTwoCanonicalSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle predecessor = false at hselected
  constructor
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.1]
    rfl
  · rw [sixVertexDegreeTwoCanonicalTransportedActiveColor,
      sixVertexDegreeTwoCanonicalTransportedColor_active, hselected.2]
    rfl

@[simp] theorem fkMedialBlackDartMaskSwap_vertex
    {T : EvenTorus} (mask : T.Vertex -> Bool) (dart : FKMedialBlackDart T) :
    (fkMedialBlackDartMaskSwap mask dart).1.1 = dart.1.1 := by
  by_cases hm : mask dart.1.1 <;>
    simp [fkMedialBlackDartMaskSwap, hm, fkMedialBlackDartSwap_self_vertex]

@[simp] theorem activeBlackDart_maskSwap_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (mask : T.Vertex -> Bool) (dart : FKMedialBlackDart T) :
    activeBlackDart (omega := omega) (eta := eta)
        (fkMedialBlackDartMaskSwap mask dart) ↔
      activeBlackDart (omega := omega) (eta := eta) dart := by
  unfold activeBlackDart
  rw [fkMedialBlackDartMaskSwap_vertex]



theorem finiteFirstReturn_togglePairingMask_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (pairing : FKMedialLoopPairing T) (mask : T.Vertex -> Bool)
    (hmask : forall (dart : FKMedialBlackDart T),
      Not (activeBlackDart (omega := omega) (eta := eta) dart) ->
        mask dart.1.1 = false)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm (fkMedialTogglePairingMask pairing mask))
        (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 =
      (finiteFirstReturn (fkMedialBlackBoundaryPerm pairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  let target := fkMedialBlackBoundaryPerm
    (fkMedialTogglePairingMask pairing mask)
  let source := fkMedialBlackBoundaryPerm pairing
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped := by
    exact (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  let x : {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
  let y : {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} :=
    ⟨swapped, hswappedActive⟩
  have htarget : target = source * fkMedialBlackDartMaskSwap mask := by
    exact fkMedialBlackBoundaryPerm_togglePairingMask pairing mask
  have hrelated := finiteFirstReturn_related_of_aligned_first target source
    (activeBlackDart (omega := omega) (eta := eta))
    (activeBlackDart (omega := omega) (eta := eta))
    (fun a b => a = b)
    (by intro a b hab; simpa [hab])
    (by
      intro a b hab ha hb
      subst b
      have hm : mask a.1.1 = false := hmask a ha
      rw [htarget]
      simp [Equiv.Perm.mul_apply, fkMedialBlackDartMaskSwap, hm])
    x y
    (by
      rw [htarget]
      simp [x, y, swapped, Equiv.Perm.mul_apply])
  exact hrelated

theorem sixVertexDegreeTwoCanonicalExpanded_firstReturn_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
    let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
    let swapped := fkMedialBlackDartMaskSwap mask dart
    (finiteFirstReturn
        (fkMedialBlackBoundaryPerm
          (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
            middle homegaSector hetaSector hmiddle layer))
        (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  rw [sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask]
  exact finiteFirstReturn_togglePairingMask_active
    (alignedRoutingLoopPairing homega heta hdegree layer) mask
    (fun d hd => sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive homega
      heta hdegree middle homegaSector hetaSector hmiddle layer d hd)
    dart hactive



theorem fkMedialBlackDartMaskSwap_targetSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) (slot : T.Vertex × Bool) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (fkMedialBlackDartMaskSwap mask
          ((fkColoredBlackDartStrandSlotEquiv
            (fkMedialTogglePairingMask pairing mask)).symm slot)) =
      fkColoredParityMaskStrandSlotSwap mask false slot := by
  let source := fkColoredBlackDartStrandSlotEquiv pairing
  let target := fkColoredBlackDartStrandSlotEquiv
    (fkMedialTogglePairingMask pairing mask)
  let blackSwap := fkColoredParityMaskStrandSlotSwap mask true
  let whiteSwap := fkColoredParityMaskStrandSlotSwap mask false
  let dart := target.symm slot
  have htarget := fkColoredBlackDartStrandSlotEquiv_togglePairingMask
    pairing mask
  have hdart : blackSwap (source dart) = slot := by
    change (source.trans blackSwap) dart = slot
    rw [← htarget]
    exact target.apply_symm_apply slot
  rw [fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap]
  change whiteSwap (blackSwap (source dart)) = whiteSwap slot
  rw [hdart]

theorem fkMedialBlackDartMaskSwap_canonicalTargetState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkMedialBlackDartMaskSwap mask
        ((fkColoredBlackDartStrandSlotEquiv
          (fkMedialTogglePairingMask
            (alignedRoutingLoopPairing homega heta hdegree layer) mask)).symm
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      doubledAlignedBlackDart homega heta hdegree layer
        (if mask (doubledAlignedVertex x) &&
            (fkMedialVertexParity (doubledAlignedVertex x) == false) then
          doubledAlignedBranchSwap x else x) := by
  apply (fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer)).injective
  rw [fkMedialBlackDartMaskSwap_targetSlot]
  simp only [doubledAlignedBlackDart,
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot]
  by_cases hm : mask (doubledAlignedVertex x) <;>
    cases hp : fkMedialVertexParity (doubledAlignedVertex x)
  · simpa [fkColoredParityMaskStrandSlotSwap, hm, hp] using
      fkColoredVertexStrandSlotSwap_doubledAlignedSlot
        homega heta hdegree layer x
  · simp [fkColoredParityMaskStrandSlotSwap, hm, hp]
  · simp [fkColoredParityMaskStrandSlotSwap, hm, hp]
  · simp [fkColoredParityMaskStrandSlotSwap, hm, hp]

theorem fkColoredParityMaskStrandSlotSwap_doubledAlignedState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredParityMaskStrandSlotSwap mask parity
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) =
      (doubledAlignedVertex
          (if mask (doubledAlignedVertex x) &&
              (fkMedialVertexParity (doubledAlignedVertex x) == parity) then
            doubledAlignedBranchSwap x else x),
        doubledAlignedSlot homega heta hdegree layer
          (if mask (doubledAlignedVertex x) &&
              (fkMedialVertexParity (doubledAlignedVertex x) == parity) then
            doubledAlignedBranchSwap x else x)) := by
  by_cases hm : mask (doubledAlignedVertex x) <;>
    cases hp : fkMedialVertexParity (doubledAlignedVertex x) <;>
    cases parity
  all_goals simp [fkColoredParityMaskStrandSlotSwap, hm, hp]
  all_goals first
    | exact fkColoredVertexStrandSlotSwap_doubledAlignedSlot
        homega heta hdegree layer x
    | rfl

noncomputable def sixVertexDegreeTwoCanonicalExpandedInputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  if mask (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == false) then
    doubledAlignedBranchSwap x else x

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedInputState_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
      homegaSector hetaSector hmiddle layer x).1 = x.1 := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask, hparity]

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedInputState_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) = x := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask, hparity]

theorem sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedBranchSwap x) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask, hparity]

noncomputable def sixVertexDegreeTwoCanonicalExpandedSourceReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (layer : Bool)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  if layer then sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta
    hdegree x else doubledAlignedFirstReturnPerm homega heta hdegree x

noncomputable def sixVertexDegreeTwoCanonicalExpandedOutputState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  if mask (doubledAlignedVertex x) &&
      (fkMedialVertexParity (doubledAlignedVertex x) == true) then
    doubledAlignedBranchSwap x else x

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedOutputState_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
      homegaSector hetaSector hmiddle layer x).1 = x.1 := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedOutputState, hmask, hparity]

@[simp] theorem sixVertexDegreeTwoCanonicalExpandedOutputState_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) = x := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedOutputState, hmask, hparity]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (doubledAlignedBranchSwap x) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex x) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex x) <;>
    simp [sixVertexDegreeTwoCanonicalExpandedOutputState, hmask, hparity]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let left := cut.cutLeft.head hleft
    let mismatch :=
      (orientedDartAlignedRetie homega heta hdegree left.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer left =
      if !mismatch &&
          (fkMedialVertexParity (doubledAlignedVertex left) == true) then
        doubledAlignedBranchSwap left else left := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let left := cut.cutLeft.head hleft
  let mismatch :=
    (orientedDartAlignedRetie homega heta hdegree left.1).pairingP !=
      (orientedDartAlignedRetie homega heta hdegree left.1).pairingQ
  change (if sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex left) &&
        (fkMedialVertexParity (doubledAlignedVertex left) == true) then
      doubledAlignedBranchSwap left else left) = _
  rw [sixVertexDegreeTwoCanonicalExpandedRetieMask_leftHead homega heta hdegree
    middle homegaSector hetaSector hmiddle hleft hright layer]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_rightHead_of_coincident
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    let mismatch :=
      (orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer right =
      if !mismatch &&
          (fkMedialVertexParity (doubledAlignedVertex right) == true) then
        doubledAlignedBranchSwap right else right := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let mismatch :=
    (orientedDartAlignedRetie homega heta hdegree right.1).pairingP !=
      (orientedDartAlignedRetie homega heta hdegree right.1).pairingQ
  change (if sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex right) &&
        (fkMedialVertexParity (doubledAlignedVertex right) == true) then
      doubledAlignedBranchSwap right else right) = _
  rw [sixVertexDegreeTwoCanonicalExpandedRetieMask_rightHead_of_coincident
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
    hvertex layer]

noncomputable def sixVertexDegreeTwoCanonicalExpandedActiveReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  let input := sixVertexDegreeTwoCanonicalExpandedInputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer x
  let returned := sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega
    heta hdegree layer input
  if mask (doubledAlignedVertex returned) &&
      (fkMedialVertexParity (doubledAlignedVertex returned) == true) then
    doubledAlignedBranchSwap returned else returned

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle layer x =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega heta
          hdegree layer
          (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
            middle homegaSector hetaSector hmiddle layer x)) := by
  rfl

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega heta
          hdegree layer x) := by
  rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_eq_output,
    sixVertexDegreeTwoCanonicalExpandedInputState_self]

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false rightPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false rightHead ∧
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false leftPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false leftHead := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  have hrightReturn : doubledAlignedFirstReturnPerm homega heta hdegree
      rightPredecessor = rightHead := by
    simp [rightPredecessor]
  have hleftReturn : doubledAlignedFirstReturnPerm homega heta hdegree
      leftPredecessor = leftHead := by
    simp [leftPredecessor]
  constructor
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simpa [sixVertexDegreeTwoCanonicalExpandedSourceReturnState,
      hrightReturn]
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simpa [sixVertexDegreeTwoCanonicalExpandedSourceReturnState,
      hleftReturn]

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer (cut.cutLeft.head hleft) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer
          (cut.cutRight.head hright)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  have hbranch :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
      hvertex
  change cut.cutLeft.head hleft =
      doubledAlignedBranchSwap (cut.cutRight.head hright) at hbranch
  change sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
      middle homegaSector hetaSector hmiddle layer (cut.cutLeft.head hleft) =
    doubledAlignedBranchSwap
      (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (cut.cutRight.head hright))
  rw [hbranch,
    sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap]

theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_coincident_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutRight.head hright)
    let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutLeft.head hleft)
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false leftPredecessor) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
          hdegree middle homegaSector hetaSector hmiddle false
          (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
            middle homegaSector hetaSector hmiddle false
            rightPredecessor)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutRight.head hright)
  let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutLeft.head hleft)
  have hreturns :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have houtputs :=
    sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints homega
      heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex
      false
  exact hreturns.2.trans (houtputs.trans (congrArg doubledAlignedBranchSwap
    hreturns.1.symm))



theorem sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer)
        ((finiteFirstReturn
          (fkMedialBlackBoundaryPerm
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer))
          (activeBlackDart (omega := omega) (eta := eta))
          ⟨dart, hactive⟩).1) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
            hdegree middle homegaSector hetaSector hmiddle layer x),
        doubledAlignedSlot homega heta hdegree layer
          (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
            hdegree middle homegaSector hetaSector hmiddle layer x)) := by
  let sourcePairing := alignedRoutingLoopPairing homega heta hdegree layer
  let mask := sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
    middle homegaSector hetaSector hmiddle layer
  let targetPairing := sixVertexDegreeTwoCanonicalExpandedTargetPairing
    homega heta hdegree middle homegaSector hetaSector hmiddle layer
  let input := sixVertexDegreeTwoCanonicalExpandedInputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer x
  let returned := sixVertexDegreeTwoCanonicalExpandedSourceReturnState homega
    heta hdegree layer input
  let swapped := fkMedialBlackDartMaskSwap mask dart
  have hpairing : targetPairing =
      fkMedialTogglePairingMask sourcePairing mask := by
    exact sixVertexDegreeTwoCanonicalExpandedTargetPairing_eq_toggleMask
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
  have hdart : dart =
      (fkColoredBlackDartStrandSlotEquiv targetPairing).symm
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
    apply (fkColoredBlackDartStrandSlotEquiv targetPairing).injective
    simpa [targetPairing] using hslot
  have hswapped : swapped =
      doubledAlignedBlackDart homega heta hdegree layer input := by
    dsimp only [swapped]
    rw [hdart, hpairing]
    exact fkMedialBlackDartMaskSwap_canonicalTargetState homega heta hdegree
      mask layer x
  have hswappedActive :
      activeBlackDart (omega := omega) (eta := eta) swapped :=
    (activeBlackDart_maskSwap_iff mask dart).mpr hactive
  have hstart :
      (⟨swapped, hswappedActive⟩ : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) =
      doubledAlignedBlackDartEquiv homega heta hdegree layer input := by
    apply Subtype.ext
    exact hswapped
  have hsourceReturn :
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨swapped, hswappedActive⟩).1 =
      doubledAlignedBlackDart homega heta hdegree layer returned := by
    rw [hstart]
    cases layer
    · exact congrArg Subtype.val
        (doubledAlignedFirstReturnPerm_false_arrival homega heta hdegree input).symm
    · exact congrArg Subtype.val
        (sixVertexDegreeTwoAlignedTrueFirstReturn_arrival homega heta hdegree
          input)
  have htargetReturn := sixVertexDegreeTwoCanonicalExpanded_firstReturn_active
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
    hactive
  change (finiteFirstReturn
      (fkMedialBlackBoundaryPerm targetPairing)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨dart, hactive⟩).1 =
    (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      ⟨swapped, hswappedActive⟩).1 at htargetReturn
  change fkColoredBlackDartStrandSlotEquiv targetPairing
      ((finiteFirstReturn
        (fkMedialBlackBoundaryPerm targetPairing)
        (activeBlackDart (omega := omega) (eta := eta))
        ⟨dart, hactive⟩).1) = _
  rw [htargetReturn, hsourceReturn, hpairing,
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask]
  simp only [Equiv.trans_apply]
  have hcoordinate :
      fkColoredBlackDartStrandSlotEquiv sourcePairing
          (doubledAlignedBlackDart homega heta hdegree layer returned) =
        (doubledAlignedVertex returned,
          doubledAlignedSlot homega heta hdegree layer returned) := by
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  rw [hcoordinate]
  rw [fkColoredParityMaskStrandSlotSwap_doubledAlignedState]
  rfl



noncomputable def sixVertexDegreeTwoTauAdjustedState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  if retie.pairingP = retie.pairingQ then x
  else doubledAlignedBranchSwap x

theorem sixVertexDegreeTwoTauAdjustedState_trueDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      doubledAlignedBlackDart homega heta hdegree false x := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [sixVertexDegreeTwoTauAdjustedState, if_pos heq]
    have h := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree x
    simpa [retie, heq] using h
  · rw [sixVertexDegreeTwoTauAdjustedState, if_neg heq]
    have h := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap x)
    simpa [retie, heq] using h

@[simp] theorem sixVertexDegreeTwoTauAdjustedState_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x).1 = x.1 := by
  change (if (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ then x
    else doubledAlignedBranchSwap x).1 = x.1
  split <;> simp

theorem sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree x = x := by
  rw [sixVertexDegreeTwoTauAdjustedState, if_pos heq]

theorem sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (hne : ¬(orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree x =
      doubledAlignedBranchSwap x := by
  rw [sixVertexDegreeTwoTauAdjustedState, if_neg hne]

@[simp] theorem sixVertexDegreeTwoTauAdjustedState_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = x := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
      homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq]
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingQ := by
      simpa only [doubledAlignedBranchSwap_fst] using heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
      homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree (doubledAlignedBranchSwap x) heq',
      doubledAlignedBranchSwap_self]

theorem sixVertexDegreeTwoTauAdjustedState_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (doubledAlignedBranchSwap x) =
      doubledAlignedBranchSwap
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · have heq' : (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingQ := by
      simpa only [doubledAlignedBranchSwap_fst] using heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
      homega heta hdegree (doubledAlignedBranchSwap x) heq',
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq]
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (doubledAlignedBranchSwap x).1).pairingQ := by
      simpa only [doubledAlignedBranchSwap_fst] using heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
      homega heta hdegree (doubledAlignedBranchSwap x) heq',
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree x heq,
      doubledAlignedBranchSwap_self]

theorem sixVertexDegreeTwoCanonicalExpandedInputState_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · have heq' : (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedInputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq _ _ _ _ heq']
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedInputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree x heq,
      sixVertexDegreeTwoCanonicalExpandedInputState_branchSwap,
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree _ heq']

theorem sixVertexDegreeTwoCanonicalExpandedOutputState_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x) := by
  by_cases heq : (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ
  · have heq' : (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedOutputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq
        homega heta hdegree x heq,
      sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq _ _ _ _ heq']
  · have heq' : ¬(orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingP =
      (orientedDartAlignedRetie homega heta hdegree
        (sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree
          middle homegaSector hetaSector hmiddle layer x).1).pairingQ := by
      rw [sixVertexDegreeTwoCanonicalExpandedOutputState_fst]
      exact heq
    rw [sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree x heq,
      sixVertexDegreeTwoCanonicalExpandedOutputState_branchSwap,
      sixVertexDegreeTwoTauAdjustedState_eq_branchSwap_of_pairing_ne
        homega heta hdegree _ heq']



noncomputable def sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
      hdegree middle homegaSector hetaSector hmiddle) : T.Vertex × Bool :=
  fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer) occurrence.1

theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) := by
  intro first second h
  apply Subtype.ext
  exact (fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer)).injective h

noncomputable def sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (i : Fin (Fintype.card
      (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle))) : T.Vertex × Bool :=
  sixVertexDegreeTwoCanonicalPhysicalBoundaryKey homega heta hdegree middle
    homegaSector hetaSector hmiddle layer
      ((Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i)

theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) :=
  (sixVertexDegreeTwoCanonicalPhysicalBoundaryKey_injective homega heta
    hdegree middle homegaSector hetaSector hmiddle layer).comp
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm.injective


theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T) :
    (∃ i, sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer i =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree layer) dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle :=
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
          homegaSector hetaSector hmiddle)).symm i
    have hdart : occurrence.1 = dart := by
      apply (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree layer)).injective
      exact hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle := ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
        homegaSector hetaSector hmiddle) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
      sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)



theorem sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
          hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
          heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree layer) dart) =
      (!layer, fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree (!layer)) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
      hdegree middle homegaSector hetaSector hmiddle := ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
      homegaSector hetaSector hmiddle) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle currentLayer i =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree currentLayer) dart := by
    unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
      sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]



theorem sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
          hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
          heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree layer) dart) =
      (layer, fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree layer) dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart ((sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart).mp
      hexists)




theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_falseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree false dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
          false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
            middle homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, fkColoredBlackDartStrandSlotEquiv
            (alignedRoutingLoopPairing homega heta hdegree true) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree false dart) := by
  classical
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hdart,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle false dart
        hdart]
    rfl
  · rw [dif_neg hdart,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle false dart
        hdart]



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_trueDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (dart : FKMedialBlackDart T) :
    let physical := alignedBlackDartLayerSwap homega heta hdegree dart
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree true dart)) =
      if _hphysical : physical ∈ doubledAlignedBoundarySegments homega heta
          hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, fkColoredBlackDartStrandSlotEquiv
            (alignedRoutingLoopPairing homega heta hdegree false) physical)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree true dart) := by
  classical
  let physical := alignedBlackDartLayerSwap homega heta hdegree dart
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
  change fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
          hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
          heta hdegree middle homegaSector hetaSector hmiddle)
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) physical)) =
    if _hphysical : physical ∈ doubledAlignedBoundarySegments homega heta
        hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) then
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) physical)
    else
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) physical)
  by_cases hphysical : physical ∈ doubledAlignedBoundarySegments homega heta
      hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hphysical,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle true
        physical hphysical]
    rfl
  · rw [dif_neg hphysical,
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle true
        physical hphysical]



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
          hdegree layer dart) := by
  classical
  have hslot (currentLayer : Bool) :
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
          currentLayer dart =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree currentLayer) dart := by
    cases currentLayer
    · exact sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false homega heta
        hdegree dart
    · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
        alignedBlackDartLayerSwap_inactive homega heta hdegree dart hinactive]
  rw [hslot layer]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree
      false (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart]
    have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    rw [hslot false, hslot true] at hcross
    cases layer
    · exact hcross.symm
    · exact hcross
  · rw [
      sixVertexDegreeTwoCanonicalPhysicalOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
        hdart]



theorem sixVertexDegreeTwoCanonicalPhysicalExpanded_falseDart_color_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
              hdegree middle homegaSector hetaSector hmiddle layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  have hmask := sixVertexDegreeTwoCanonicalExpandedRetieMask_inactive homega
    heta hdegree middle homegaSector hetaSector hmiddle layer dart hdart
  rw [sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart_of_unmasked homega
      heta hdegree middle homegaSector hetaSector hmiddle layer dart hmask
      hnext,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
      (alignedBoundaryPerm homega heta hdegree false dart) hnext,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart]
  exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
    homega heta hdegree layer dart hnext



theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle x hx) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
        doubledAlignedSlot homega heta hdegree true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) := by
  unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
    sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    sixVertexDegreeTwoAlignedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)
      (doubledAlignedBlackDart homega heta hdegree false x) = _
  rw [← sixVertexDegreeTwoTauAdjustedState_trueDart
    homega heta hdegree x]
  exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _

theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle x hx) =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree false x) := by
  unfold sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey
    sixVertexDegreeTwoCanonicalPhysicalBoundaryKey
    sixVertexDegreeTwoAlignedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _

noncomputable def sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) : Bool :=
  fkColoredLayeredSlotColor
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
    (fkIndexedOccurrenceSlotEquiv
      (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta
        hdegree middle homegaSector hetaSector hmiddle)
      (layer, doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_activeDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (doubledAlignedBlackDart homega heta hdegree false x))) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer x := by
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active]
  rfl



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer))
      (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) arrival)) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
          hdegree middle homegaSector hetaSector hmiddle layer x) := by
  let arrival := (finiteFirstReturn
    (fkMedialBlackBoundaryPerm
      (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer))
    (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1
  have hreturn := sixVertexDegreeTwoCanonicalExpanded_firstReturn_slot homega
    heta hdegree middle homegaSector hetaSector hmiddle layer x dart hactive
    hslot
  dsimp only
  unfold sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor
  rw [hreturn]



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) dart)) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer x := by
  unfold sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor
  rw [hslot]

theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_of_activeState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) (dart : FKMedialBlackDart T)
    (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
    (hslot : fkColoredBlackDartStrandSlotEquiv
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) dart =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x))
    (hcolor : sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta
          hdegree middle homegaSector hetaSector hmiddle layer x) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle layer x) :
    let arrival := (finiteFirstReturn
      (fkMedialBlackBoundaryPerm
        (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
          middle homegaSector hetaSector hmiddle layer))
      (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) arrival)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
            heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
            hdegree middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega
            heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, fkColoredBlackDartStrandSlotEquiv
            (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta
              hdegree middle homegaSector hetaSector hmiddle layer) dart)) := by
  dsimp only
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedColor_firstReturn_slot
      homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart
      hactive hslot,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_targetStart_slot
      homega heta hdegree middle homegaSector hetaSector hmiddle layer x dart
      hslot]
  exact hcolor



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false x =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  let i := sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
    middle homegaSector hetaSector hmiddle x hx
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor,
    ← sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false
      homega heta hdegree middle homegaSector hetaSector hmiddle x hx]
  rw [fkIndexedOccurrenceSlotEquiv_apply_key]
  simp only [Bool.not_false]
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState]
  rfl



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
  let i := sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
    middle homegaSector hetaSector hmiddle x hx
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor,
    ← sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState
      homega heta hdegree middle homegaSector hetaSector hmiddle x hx]
  rw [fkIndexedOccurrenceSlotEquiv_apply_key]
  simp only [Bool.not_true]
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState_false]
  rfl



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false x =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor]
  have hnot : ¬ ∃ i,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle false i =
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) := by
    intro hex
    have hrange := (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle false
      (doubledAlignedBlackDart homega heta hdegree false x)).mp (by
        rcases hex with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        calc
          _ = (doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree false x) := hi
          _ = fkColoredBlackDartStrandSlotEquiv
                (alignedRoutingLoopPairing homega heta hdegree false)
                (doubledAlignedBlackDart homega heta hdegree false x) := by
            change _ = fkColoredBlackDartStrandSlotEquiv
              (alignedRoutingLoopPairing homega heta hdegree false)
              (blackDartOfStrandSlot
                (alignedRoutingLoopPairing homega heta hdegree false)
                (doubledAlignedVertex x,
                  doubledAlignedSlot homega heta hdegree false x))
            exact (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
              (alignedRoutingLoopPairing homega heta hdegree false) _).symm)
    exact hx ((doubledAlignedBlackDart_mem_boundarySegments_iff homega heta
      hdegree false _ x).mp hrange)
  rw [fkIndexedOccurrenceSlotEquiv_apply_of_not_routed _ _ _ _ hnot]
  rfl



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor]
  have hcoordinate :
      (doubledAlignedVertex
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
        doubledAlignedSlot homega heta hdegree true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedBlackDart homega heta hdegree false x) := by
    rw [← sixVertexDegreeTwoTauAdjustedState_trueDart]
    exact (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _).symm
  have hnot : ¬ ∃ i,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle true i =
        (doubledAlignedVertex
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)) := by
    rw [hcoordinate]
    intro hex
    have hrange := (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_exists_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle true
      (doubledAlignedBlackDart homega heta hdegree false x)).mp hex
    exact hx ((doubledAlignedBlackDart_mem_boundarySegments_iff homega heta
      hdegree false _ x).mp hrange)
  rw [fkIndexedOccurrenceSlotEquiv_apply_of_not_routed _ _ _ _ hnot]
  rfl



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false x =
      if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x := by
  by_cases hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle
  · rw [dif_pos hx,
      sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
        homega heta hdegree middle homegaSector hetaSector hmiddle x hx]
  · rw [dif_neg hx,
      sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
        homega heta hdegree middle homegaSector hetaSector hmiddle x hx]



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true x =
      if _hx : sixVertexDegreeTwoTauAdjustedState homega heta hdegree x ∈
          SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x)
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x := by
  let tx := sixVertexDegreeTwoTauAdjustedState homega heta hdegree x
  by_cases hx : tx ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle
  · rw [dif_pos hx]
    have h := sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle tx hx
    simpa [tx] using h
  · rw [dif_neg hx]
    have h := sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle tx hx
    simpa [tx] using h



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) =
      if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
          middle homegaSector hetaSector hmiddle then
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x
      else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) := by
  rw [sixVertexDegreeTwoCanonicalPhysicalTransportedColor_true]
  simp





theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_input_false_defect
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    (htransition : sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree
      middle homegaSector hetaSector hmiddle (doubledAlignedVertex x) = false)
    (hpairing :
      (orientedDartAlignedRetie homega heta hdegree x.1).pairingP =
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) :
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x !=
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false x)) = !x.2 := by
  have hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta hdegree
      middle homegaSector hetaSector hmiddle false
        (doubledAlignedVertex x) = false := by
    rw [sixVertexDegreeTwoCanonicalExpandedRetieMask_activeState]
    simp [htransition, hx, hpairing]
  have hinput : sixVertexDegreeTwoCanonicalExpandedInputState homega heta
      hdegree middle homegaSector hetaSector hmiddle false x = x := by
    simp [sixVertexDegreeTwoCanonicalExpandedInputState, hmask]
  have htau : sixVertexDegreeTwoTauAdjustedState homega heta hdegree x = x :=
    sixVertexDegreeTwoTauAdjustedState_eq_self_of_pairing_eq homega heta hdegree
      x hpairing
  rw [hinput, sixVertexDegreeTwoCanonicalPhysicalTransportedColor_false]
  simp only [hx, dif_pos, htau]
  have hcross := sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne homega
    heta hdegree x
  change (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false x !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true x) =
    (if x.2 then
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) &&
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2)
    else
      ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP ==
        (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) ||
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2)) at hcross
  rw [hpairing] at hcross
  simpa using hcross



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutRight.head hright
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false head =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false head ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false predecessor =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
            predecessor := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutRight.head hright
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have htransition := cut.rightHead_transition homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright
  have hhead : head ∉ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := htransition.1
  have hpredecessor : predecessor ∈
      SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle := htransition.2
  exact ⟨
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor⟩



theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let head := cut.cutLeft.head hleft
    let predecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false head =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false predecessor =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
            predecessor ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree head) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false head ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) =
          sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree predecessor) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let head := cut.cutLeft.head hleft
  let predecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm head
  have htransition := cut.leftHead_transition homega heta hdegree middle
    homegaSector hetaSector hmiddle hleft hright
  have hhead : head ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := htransition.1
  have hpredecessor : predecessor ∉
      SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle := htransition.2
  exact ⟨
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_false
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_selected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle head hhead,
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_unselected_true
      homega heta hdegree middle homegaSector hetaSector hmiddle predecessor
        hpredecessor⟩




theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree
            rightPredecessor) =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false rightHead ∧
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false leftPredecessor =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  have hrightColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hleftColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hrightFirst :
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          rightPredecessor =
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          rightHead := by
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
      homega heta hdegree rightPredecessor
    simpa [sixVertexDegreeTwoAlignedActiveColor, rightPredecessor, rightHead]
      using h
  have hleftFirst :
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          leftPredecessor =
        sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
          leftHead := by
    have h := sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
      homega heta hdegree leftPredecessor
    simpa [sixVertexDegreeTwoAlignedActiveColor, leftPredecessor, leftHead]
      using h
  exact ⟨
    hrightColors.2.2.2.trans (hrightFirst.trans hrightColors.1.symm),
    hleftColors.2.1.trans (hleftFirst.trans hleftColors.2.2.1.symm)⟩




theorem sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_network
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    let common :=
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle false rightHead
    common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree
            rightPredecessor) ∧
    common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle false
          leftPredecessor ∧
    common = sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega
        heta hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  let common :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
      hdegree middle homegaSector hetaSector hmiddle false rightHead
  have hstitch :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_endpoint_false_stitch
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hrightColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_rightHead homega heta
      hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hleftColors :=
    sixVertexDegreeTwoCanonicalPhysicalTransportedColor_leftHead homega heta
      hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hrightMem : rightHead ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inr (List.head_mem hright)
  have hleftMem : leftHead ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inl (List.head_mem hleft)
  have hstateCycle :
      (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle
        rightHead leftHead :=
    alignedPermOrderedAllOrbitLists_sameCycle_of_mem
      (doubledAlignedFirstReturnPerm homega heta hdegree) cut.cut
      (cut.cut_mem homega heta hdegree middle homegaSector hetaSector hmiddle)
      hrightMem hleftMem
  have hfalseCycle := doubledAlignedFirstReturnPerm_sameCycle_falseBoundary
    homega heta hdegree hstateCycle
  have hfalseDartColor :
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false rightHead).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false leftHead).1 := by
    obtain ⟨n, hn⟩ := hfalseCycle.exists_nat_pow_eq
    have hcolor := (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree false).color_blackBoundaryPerm_pow
        (doubledAlignedBlackDart homega heta hdegree false rightHead) n
    change
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (((alignedBoundaryPerm homega heta hdegree false) ^ n)
            (doubledAlignedBlackDart homega heta hdegree false rightHead)).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false rightHead).1 at hcolor
    rw [hn] at hcolor
    exact hcolor.symm
  have hfalse : sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      rightHead = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        leftHead := by
    rw [sixVertexDegreeTwoAlignedActiveColor,
      sixVertexDegreeTwoAlignedActiveColor,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false rightHead,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false leftHead]
    exact hfalseDartColor
  have hcommonLeft : common =
      sixVertexDegreeTwoCanonicalPhysicalTransportedActiveColor homega heta
        hdegree middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) :=
    hrightColors.1.trans (hfalse.trans hleftColors.2.2.1.symm)
  exact ⟨hstitch.1.symm,
    hcommonLeft.trans hstitch.2.symm,
    hcommonLeft⟩



theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_rightHead_table
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let v := doubledAlignedVertex (cut.cutRight.head hright)
    let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
        sixVertexDisagreementDart_local_card_eq_two hdegree
          (cut.cutRight.head hright).1
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (if selected then !retie.pairingQ else retie.pairingP,
        if selected then !retie.pairingP else retie.pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let v := doubledAlignedVertex (cut.cutRight.head hright)
  let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree
      (cut.cutRight.head hright).1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  have htable := sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    homega heta hdegree middle homegaSector hetaSector hmiddle v hactive
  have htransition := sixVertexDegreeTwoCanonicalTransitionMask_rightHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v = true at htransition
  simpa [htransition] using htable



theorem sixVertexDegreeTwoCanonicalExpandedTargetPairing_leftHead_table
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let v := doubledAlignedVertex (cut.cutLeft.head hleft)
    let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
        sixVertexDisagreementDart_local_card_eq_two hdegree
          (cut.cutLeft.head hleft).1
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v
    (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (if selected then !retie.pairingQ else retie.pairingP,
        if selected then !retie.pairingP else retie.pairingQ) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let v := doubledAlignedVertex (cut.cutLeft.head hleft)
  let hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree
      (cut.cutLeft.head hleft).1
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let selected := sixVertexDegreeTwoCanonicalSelectedVertex homega heta
    hdegree middle homegaSector hetaSector hmiddle v
  have htable := sixVertexDegreeTwoCanonicalExpandedTargetPairing_active_table
    homega heta hdegree middle homegaSector hetaSector hmiddle v hactive
  have htransition := sixVertexDegreeTwoCanonicalTransitionMask_leftHead
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  change sixVertexDegreeTwoCanonicalTransitionMask homega heta hdegree middle
      homegaSector hetaSector hmiddle v = true at htransition
  simpa [htransition] using htable




theorem sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let right := cut.cutRight.head hright
    let left := cut.cutLeft.head hleft
    left = doubledAlignedBranchSwap right ∧
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false right =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false left ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true right !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true left) =
        true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let left := cut.cutLeft.head hleft
  have hbranch : left = doubledAlignedBranchSwap right :=
    canonicalDoubledAlignedCut_leftHead_eq_branchSwap_rightHead_of_vertex_eq
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
      hvertex
  have hrightMem : right ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inr (List.head_mem hright)
  have hleftMem : left ∈ cut.cut := by
    rw [cut.cut_eq, List.mem_append]
    exact Or.inl (List.head_mem hleft)
  have hstateCycle :
      (doubledAlignedFirstReturnPerm homega heta hdegree).SameCycle
        right left :=
    alignedPermOrderedAllOrbitLists_sameCycle_of_mem
      (doubledAlignedFirstReturnPerm homega heta hdegree) cut.cut
      (cut.cut_mem homega heta hdegree middle homegaSector hetaSector hmiddle)
      hrightMem hleftMem
  have hfalseCycle := doubledAlignedFirstReturnPerm_sameCycle_falseBoundary
    homega heta hdegree hstateCycle
  have hfalseDartColor :
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false right).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false left).1 := by
    obtain ⟨n, hn⟩ := hfalseCycle.exists_nat_pow_eq
    have hcolor := (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree false).color_blackBoundaryPerm_pow
        (doubledAlignedBlackDart homega heta hdegree false right) n
    change
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (((alignedBoundaryPerm homega heta hdegree false) ^ n)
            (doubledAlignedBlackDart homega heta hdegree false right)).1 =
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
          (doubledAlignedBlackDart homega heta hdegree false right).1 at hcolor
    rw [hn] at hcolor
    exact hcolor.symm
  have hfalse : sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      right = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        left := by
    rw [sixVertexDegreeTwoAlignedActiveColor,
      sixVertexDegreeTwoAlignedActiveColor,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false right,
      ← sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
        homega heta hdegree false left]
    exact hfalseDartColor
  have hfalseSwap :
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex right,
            doubledAlignedSlot homega heta hdegree false right) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex (doubledAlignedBranchSwap right),
            doubledAlignedSlot homega heta hdegree false
              (doubledAlignedBranchSwap right)) := by
    change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      right = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        (doubledAlignedBranchSwap right)
    rw [← hbranch]
    exact hfalse
  have htrue :=
    sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq
      homega heta hdegree right hfalseSwap
  refine ⟨hbranch, hfalse, ?_⟩
  change (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
      right != sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        left) = true
  rw [hbranch]
  exact htrue

theorem sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft))
    (layer : Bool) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
      (cut.cutRight.head hright)
    let leftOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
      (cut.cutLeft.head hleft)
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false rightOut =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false leftOut ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightOut !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftOut) =
        true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let right := cut.cutRight.head hright
  let left := cut.cutLeft.head hleft
  let rightOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer right
  let leftOut := sixVertexDegreeTwoCanonicalExpandedOutputState homega heta
    hdegree middle homegaSector hetaSector hmiddle layer left
  have hcolors := sixVertexDegreeTwoCanonicalCoincidentEndpoint_sourceColors
    homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
    hvertex
  dsimp only at hcolors
  have houtputs :=
    sixVertexDegreeTwoCanonicalExpandedOutputState_coincident_endpoints homega
      heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex
      layer
  change leftOut = doubledAlignedBranchSwap rightOut at houtputs
  change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      rightOut = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        leftOut ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightOut !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftOut) =
        true
  rw [houtputs]
  have hfalse := hcolors.2.1
  have htrue := hcolors.2.2
  rw [hcolors.1] at hfalse htrue
  change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false right =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
        (doubledAlignedBranchSwap right) at hfalse
  change (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true right !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true
        (doubledAlignedBranchSwap right)) = true at htrue
  cases hmask : sixVertexDegreeTwoCanonicalExpandedRetieMask homega heta
      hdegree middle homegaSector hetaSector hmiddle layer
        (doubledAlignedVertex right) <;>
    cases hparity : fkMedialVertexParity (doubledAlignedVertex right) <;>
    simp [rightOut, sixVertexDegreeTwoCanonicalExpandedOutputState, hmask,
      hparity, hfalse, htrue, bne_comm]

theorem sixVertexDegreeTwoCanonicalCoincidentEndpoint_activeReturnSourceColors
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (hvertex : doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright) =
      doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutRight.head hright)
    let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
      (cut.cutLeft.head hleft)
    let rightReturn :=
      sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false rightPredecessor)
    let leftReturn :=
      sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle false
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle false leftPredecessor)
    sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false rightReturn =
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false leftReturn ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightReturn !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftReturn) =
        true := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutRight.head hright)
  let leftPredecessor := (doubledAlignedFirstReturnPerm homega heta hdegree).symm
    (cut.cutLeft.head hleft)
  let rightReturn :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
      middle homegaSector hetaSector hmiddle false
      (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false rightPredecessor)
  let leftReturn :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
      middle homegaSector hetaSector hmiddle false
      (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree middle
        homegaSector hetaSector hmiddle false leftPredecessor)
  have hreturns :=
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_false_endpoints
      homega heta hdegree middle homegaSector hetaSector hmiddle hleft hright
  have hcolors :=
    sixVertexDegreeTwoCanonicalCoincidentEndpoint_outputSourceColors homega
      heta hdegree middle homegaSector hetaSector hmiddle hleft hright hvertex
      false
  rcases hreturns with ⟨hrightReturn, hleftReturn⟩
  change rightReturn = sixVertexDegreeTwoCanonicalExpandedOutputState homega
      heta hdegree middle homegaSector hetaSector hmiddle false
        (cut.cutRight.head hright) at hrightReturn
  change leftReturn = sixVertexDegreeTwoCanonicalExpandedOutputState homega
      heta hdegree middle homegaSector hetaSector hmiddle false
        (cut.cutLeft.head hleft) at hleftReturn
  change sixVertexDegreeTwoAlignedActiveColor homega heta hdegree false
      rightReturn = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree
        false leftReturn ∧
    (sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true rightReturn !=
      sixVertexDegreeTwoAlignedActiveColor homega heta hdegree true leftReturn) =
        true
  rw [hrightReturn, hleftReturn]
  dsimp only at hcolors
  exact hcolors



theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hy : doubledAlignedFirstReturnPerm homega heta hdegree x ∈
      SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle
          (doubledAlignedFirstReturnPerm homega heta hdegree x) hy) =
      (doubledAlignedVertex
          (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x),
        doubledAlignedSlot homega heta hdegree true
          (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
            x)) := by
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState]
  rfl



theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_proper_interior
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ [])
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    (hexit : x ≠ (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft.getLast hleft) :
    let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    ∃ hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
        middle homegaSector hetaSector hmiddle,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
            middle homegaSector hetaSector hmiddle y hy) =
        (doubledAlignedVertex
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  have hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := by
    have hiff := cut.selected_mem_iff homega heta hdegree middle homegaSector
      hetaSector hmiddle hleft hright x
    exact hiff.mpr (Or.inl ⟨hx, hexit⟩)
  exact ⟨hy,
    sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_sigma_of_mem homega heta
      hdegree middle homegaSector hetaSector hmiddle x hy⟩

@[simp] theorem sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree x =
      sixVertexDegreeTwoTauAdjustedState homega heta hdegree
        (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  rfl




theorem sixVertexDegreeTwoCanonicalExpandedActiveReturnState_proper_true_endpoints
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle).cutRight ≠ []) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
      homegaSector hetaSector hmiddle
    let rightHead := cut.cutRight.head hright
    let rightPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
    let leftHead := cut.cutLeft.head hleft
    let leftPredecessor :=
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle true rightPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree rightHead) ∧
    sixVertexDegreeTwoCanonicalExpandedActiveReturnState homega heta hdegree
        middle homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoCanonicalExpandedInputState homega heta hdegree
          middle homegaSector hetaSector hmiddle true leftPredecessor) =
      sixVertexDegreeTwoCanonicalExpandedOutputState homega heta hdegree middle
        homegaSector hetaSector hmiddle true
        (sixVertexDegreeTwoTauAdjustedState homega heta hdegree leftHead) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let rightHead := cut.cutRight.head hright
  let rightPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm rightHead
  let leftHead := cut.cutLeft.head hleft
  let leftPredecessor :=
    (doubledAlignedFirstReturnPerm homega heta hdegree).symm leftHead
  constructor
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simp [sixVertexDegreeTwoCanonicalExpandedSourceReturnState]
  · rw [sixVertexDegreeTwoCanonicalExpandedActiveReturnState_input]
    simp [sixVertexDegreeTwoCanonicalExpandedSourceReturnState]



theorem sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_emptyCut_sigma
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hempty :
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutLeft = [] \/
      (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
        homegaSector hetaSector hmiddle).cutRight = [])
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    ∃ hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
        middle homegaSector hetaSector hmiddle,
      sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle true
          (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
            middle homegaSector hetaSector hmiddle y hy) =
        (doubledAlignedVertex
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoAlignedTrueFirstReturnState homega heta hdegree
              x)) := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  have hy : y ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle := by
    rcases hempty with hleft | hright
    · exact (cut.selected_invariant_of_left_empty homega heta hdegree middle
        homegaSector hetaSector hmiddle hleft x).mpr hx
    · exact (cut.selected_invariant_of_right_empty homega heta hdegree middle
        homegaSector hetaSector hmiddle hright x).mpr hx
  refine ⟨hy, ?_⟩
  rw [sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_selectedState]
  simp only [sixVertexDegreeTwoAlignedTrueFirstReturnState_eq_tauAdjusted]



theorem sixVertexDegreeTwoCanonicalPhysicalExpandedSlotColorInvariant_of_falseDart
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
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
              hdegree middle homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective
              homega heta hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer
              (sixVertexDegreeTwoCanonicalExpandedBoundaryFalseDart homega heta
                hdegree middle homegaSector hetaSector hmiddle layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (fkIndexedOccurrenceSlotEquiv
            (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega
              heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta
              hdegree middle homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective
              homega heta hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega
              heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoCanonicalExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta
        hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoCanonicalPhysicalBoundaryFinKey_injective homega heta
        hdegree middle homegaSector hetaSector hmiddle) := by
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

end

end StatMech.FrontierD
