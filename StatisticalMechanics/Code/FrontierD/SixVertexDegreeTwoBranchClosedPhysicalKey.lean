/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Code.FrontierD.SixVertexDegreeTwoCanonicalExpandedActive

namespace StatMech.FrontierD

noncomputable section




theorem sixVertexDegreeTwoBranchClosedUnitPrefix_tauAdjusted_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoTauAdjustedState homega heta hdegree x ∈
        sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle ↔
      x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
        middle homegaSector hetaSector hmiddle := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases heq : retie.pairingP = retie.pairingQ
  · simp [sixVertexDegreeTwoTauAdjustedState, retie, heq]
  · rw [sixVertexDegreeTwoTauAdjustedState, if_neg heq]
    exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle x


noncomputable def sixVertexDegreeTwoBranchClosedTransitionBit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) : Bool :=
  sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle x !=
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle
      ((doubledAlignedFirstReturnPerm homega heta hdegree).symm x)



def sixVertexDegreeTwoBranchClosedSynchronizedAt
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta) :
    Prop :=
  sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
      homegaSector hetaSector hmiddle (d, false) =
    sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
      homegaSector hetaSector hmiddle (d, true)



theorem sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta)
    (hunsync : ¬ sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta
      hdegree middle homegaSector hetaSector hmiddle d)
    (mask : Bool) :
    (mask != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree
        middle homegaSector hetaSector hmiddle (d, false)) = true \/
      (mask != sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree
        middle homegaSector hetaSector hmiddle (d, true)) = true := by
  unfold sixVertexDegreeTwoBranchClosedSynchronizedAt at hunsync
  cases hfalse : sixVertexDegreeTwoBranchClosedTransitionBit homega heta
      hdegree middle homegaSector hetaSector hmiddle (d, false) <;>
    cases htrue : sixVertexDegreeTwoBranchClosedTransitionBit homega heta
      hdegree middle homegaSector hetaSector hmiddle (d, true) <;>
    cases mask <;> simp_all



theorem sixVertexDegreeTwoBranchClosedExpandedRetieMask_misses_transition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta)
    (hunsync : ¬ sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta
      hdegree middle homegaSector hetaSector hmiddle d)
    (layer : Bool) :
    ∃ branch : Bool,
      (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer d.1.1.1 !=
        sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
          homegaSector hetaSector hmiddle (d, branch)) = true := by
  have hmismatch := sixVertexDegreeTwoBranchClosed_unsynchronized_no_vertex_mask
    homega heta hdegree middle homegaSector hetaSector hmiddle d hunsync
    (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer d.1.1.1)
  rcases hmismatch with hfalse | htrue
  · exact ⟨false, hfalse⟩
  · exact ⟨true, htrue⟩



theorem sixVertexDegreeTwoBranchClosedTransitionVertex_eq_bit_of_synchronized
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (d : SixVertexOrientedDisagreementDart omega eta)
    (hsync : sixVertexDegreeTwoBranchClosedSynchronizedAt homega heta hdegree
      middle homegaSector hetaSector hmiddle d) :
    sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle
        homegaSector hetaSector hmiddle d.1.1.1 =
      sixVertexDegreeTwoBranchClosedTransitionBit homega heta hdegree middle
        homegaSector hetaSector hmiddle (d, false) := by
  have hactive := sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  let d0 := orientedDisagreementDartAtActiveVertex homega heta d.1.1.1 hactive
  have hd0 : d0 = d := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d0 d rfl
  unfold sixVertexDegreeTwoBranchClosedTransitionVertex
  rw [dif_pos hactive]
  dsimp only
  change orientedDisagreementDartAtActiveVertex homega heta d.1.1.1 hactive = d
    at hd0
  rw [hd0]
  unfold sixVertexDegreeTwoBranchClosedSynchronizedAt at hsync
  unfold sixVertexDegreeTwoBranchClosedTransitionBit at hsync ⊢
  rw [hsync, Bool.or_self]



noncomputable def sixVertexDegreeTwoBranchClosedPhysicalRetieMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (_layer : Bool) (v : T.Vertex) : Bool :=
  sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle
      homegaSector hetaSector hmiddle v !=
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex homega heta hdegree
      middle homegaSector hetaSector hmiddle v

noncomputable def sixVertexDegreeTwoBranchClosedPhysicalTargetPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) : FKMedialLoopPairing T :=
  fkMedialTogglePairingMask
    (alignedRoutingLoopPairing homega heta hdegree layer)
    (sixVertexDegreeTwoBranchClosedPhysicalRetieMask homega heta hdegree
      middle homegaSector hetaSector hmiddle layer)

@[simp] theorem sixVertexDegreeTwoBranchClosedPhysicalRetieMask_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    sixVertexDegreeTwoBranchClosedPhysicalRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v = false := by
  have hnot : Not ((sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) := by omega
  simp [sixVertexDegreeTwoBranchClosedPhysicalRetieMask,
    sixVertexDegreeTwoBranchClosedTransitionVertex,
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex, hnot]



noncomputable def sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta
      hdegree middle homegaSector hetaSector hmiddle) : T.Vertex × Bool :=
  fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer) occurrence.1

theorem sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) := by
  intro first second h
  apply Subtype.ext
  exact (fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer)).injective h

noncomputable def sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (i : Fin (Fintype.card
      (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle))) : T.Vertex × Bool :=
  sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey homega heta hdegree middle
    homegaSector hetaSector hmiddle layer
      ((Fintype.equivFin
        (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i)

theorem sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) :=
  (sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey_injective homega heta
    hdegree middle homegaSector hetaSector hmiddle layer).comp
      (Fintype.equivFin
        (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm.injective



noncomputable def sixVertexDegreeTwoBranchClosedSelectedStateFinIndex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    Fin (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle)) :=
  Fintype.equivFin
    (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    ⟨doubledAlignedBlackDart homega heta hdegree false x,
      (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mpr hx⟩

theorem sixVertexDegreeTwoBranchClosedPhysicalFinKey_selected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta)
    (hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
      middle homegaSector hetaSector hmiddle) :
    sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoBranchClosedSelectedStateFinIndex homega heta
          hdegree middle homegaSector hetaSector hmiddle x hx) =
      if layer then
        (doubledAlignedVertex
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x),
          doubledAlignedSlot homega heta hdegree true
            (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x))
      else
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) := by
  unfold sixVertexDegreeTwoBranchClosedPhysicalBoundaryFinKey
    sixVertexDegreeTwoBranchClosedPhysicalBoundaryKey
    sixVertexDegreeTwoBranchClosedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree layer)
      (doubledAlignedBlackDart homega heta hdegree false x) = _
  cases layer
  · exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _
  · rw [← sixVertexDegreeTwoTauAdjustedState_trueDart
      homega heta hdegree x]
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot _ _


theorem sixVertexDegreeTwoBranchClosedPhysicalTargetPairing_noTransition
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
    (htransition : sixVertexDegreeTwoBranchClosedTransitionVertex homega heta
      hdegree middle homegaSector hetaSector hmiddle v = false)
    (hselected :
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (orientedDisagreementDartAtActiveVertex homega heta v hactive,
          false) = true) :
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    (sixVertexDegreeTwoBranchClosedPhysicalTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle false v,
      sixVertexDegreeTwoBranchClosedPhysicalTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle true v) =
      (retie.pairingQ, retie.pairingP) := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  let retie := orientedDartAlignedRetie homega heta hdegree d
  have hP := alignedRoutingPairing_eq_at_active homega heta hdegree false v
    hactive
  have hQ := alignedRoutingPairing_eq_at_active homega heta hdegree true v
    hactive
  change alignedRoutingLoopPairing homega heta hdegree false v =
    retie.pairingP at hP
  change alignedRoutingLoopPairing homega heta hdegree true v =
    retie.pairingQ at hQ
  change ((if _ != _ then !_ else _), (if _ != _ then !_ else _)) = _
  rw [hP, hQ]
  simp [sixVertexDegreeTwoBranchClosedPhysicalRetieMask, htransition,
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex, hactive, hselected]
  cases retie.pairingP <;> cases retie.pairingQ <;> decide

end

end StatMech.FrontierD
