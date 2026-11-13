/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexAlignedFirstReturn
import Code.FrontierD.SixVertexStrandSlotBoundary










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexDegreeTwoAlignedSlotRouteActiveDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _

theorem fkColoredSideSlot_eq_strandSlotOfBlackDart
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (dart : FKMedialBlackDart T) :
    fkColoredSideSlot (pairing dart.1.1) dart.1.2 =
      strandSlotOfBlackDart pairing dart := by
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases side <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;>
    simp [fkColoredSideSlot, strandSlotOfBlackDart,
      fkMedialBlackSideIndex, fkMedialCheckerColor,
      fkMedialSideVertical, hp, hv] at hdart ⊢

@[simp] theorem strandSlotOfBlackDart_blackDartOfStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) :
    strandSlotOfBlackDart pairing
        (blackDartOfStrandSlot pairing slot) = slot.2 := by
  let factor := fkMedialVertexParity slot.1 && !pairing slot.1
  have hfixed := congrArg Prod.snd
    ((fkMedialBlackDartEquivVertexBool T).apply_symm_apply
      (slot.1, blackSideIndexOfStrandSlot
        (fkMedialVertexParity slot.1) (pairing slot.1) slot.2))
  change fkMedialBlackSideIndex
      (blackDartOfStrandSlot pairing slot).1.2 =
    blackSideIndexOfStrandSlot
      (fkMedialVertexParity slot.1) (pairing slot.1) slot.2 at hfixed
  unfold strandSlotOfBlackDart
  rw [blackDartOfStrandSlot_vertex, hfixed]
  cases hp : pairing slot.1 <;>
    cases hv : fkMedialVertexParity slot.1 <;>
    cases hs : slot.2 <;>
    simp [blackSideIndexOfStrandSlot]

@[simp] theorem fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (blackDartOfStrandSlot pairing slot) = slot := by
  apply Prod.ext
  · exact blackDartOfStrandSlot_vertex pairing slot
  · rw [fkColoredBlackDartStrandSlotEquiv_apply]
    change fkColoredSideSlot
        (pairing (blackDartOfStrandSlot pairing slot).1.1)
        (blackDartOfStrandSlot pairing slot).1.2 = slot.2
    rw [fkColoredSideSlot_eq_strandSlotOfBlackDart,
      strandSlotOfBlackDart_blackDartOfStrandSlot]

@[simp] theorem fkColoredVertexStrandSlotSwap_doubledAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    fkColoredVertexStrandSlotSwap (doubledAlignedVertex x)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) =
      (doubledAlignedVertex (doubledAlignedBranchSwap x),
        doubledAlignedSlot homega heta hdegree layer
          (doubledAlignedBranchSwap x)) := by
  rw [doubledAlignedVertex_branchSwap,
    doubledAlignedSlot_branchSwap]
  rcases doubledAlignedVertex x with ⟨i, j⟩
  cases hs : doubledAlignedSlot homega heta hdegree layer x <;>
    simp [fkColoredVertexStrandSlotSwap]



theorem fkMedialBlackDartSwap_doubledAlignedBlackDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    fkMedialBlackDartSwap (doubledAlignedVertex x)
        (doubledAlignedBlackDart homega heta hdegree layer x) =
      doubledAlignedBlackDart homega heta hdegree layer
        (doubledAlignedBranchSwap x) := by
  apply (fkColoredBlackDartStrandSlotEquiv
    (alignedRoutingLoopPairing homega heta hdegree layer)).injective
  rw [fkColoredBlackDartStrandSlot_blackSwap]
  simp only [doubledAlignedBlackDart,
    fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot]
  exact fkColoredVertexStrandSlotSwap_doubledAlignedSlot
    homega heta hdegree layer x

theorem blackSideIndex_boundaryAlignedSlotQRaw
    (pairingP pairingQ vertexParity branch : Bool) (d : Fin 4) :
    blackSideIndexOfStrandSlot vertexParity pairingQ
        (if branch then
          !boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d
        else boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) =
      if pairingP = pairingQ then
        blackSideIndexOfStrandSlot vertexParity pairingP
          (if branch then !strandSlot pairingP d else strandSlot pairingP d)
      else
        blackSideIndexOfStrandSlot vertexParity pairingP
          (if !branch then !strandSlot pairingP d else strandSlot pairingP d) := by
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;>
    cases branch <;> fin_cases d <;>
      decide




theorem doubledAlignedBlackDart_true_eq_false_or_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    doubledAlignedBlackDart homega heta hdegree true x =
      if retie.pairingP = retie.pairingQ then
        doubledAlignedBlackDart homega heta hdegree false x
      else
        doubledAlignedBlackDart homega heta hdegree false
          (doubledAlignedBranchSwap x) := by
  rcases x with ⟨d, branch⟩
  let retie := orientedDartAlignedRetie homega heta hdegree d
  let v := d.1.1.1
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  let d0 := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hd0 : d0 = d := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d0 d rfl
  have hP := alignedRoutingPairing_eq_at_active
    homega heta hdegree false v hactive
  have hQ := alignedRoutingPairing_eq_at_active
    homega heta hdegree true v hactive
  change alignedRoutingLoopPairing homega heta hdegree false v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingP at hP
  change alignedRoutingLoopPairing homega heta hdegree true v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingQ at hQ
  rw [hd0] at hP hQ
  change doubledAlignedBlackDart homega heta hdegree true (d, branch) =
    if retie.pairingP = retie.pairingQ then
      doubledAlignedBlackDart homega heta hdegree false (d, branch)
    else doubledAlignedBlackDart homega heta hdegree false
      (doubledAlignedBranchSwap (d, branch))
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq]
    apply (fkMedialBlackDartEquivVertexBool T).injective
    simp only [doubledAlignedBlackDart, blackDartOfStrandSlot,
      Equiv.apply_symm_apply, doubledAlignedVertex, doubledAlignedSlot]
    rw [hP, hQ]
    apply Prod.ext
    · rfl
    · have h := blackSideIndex_boundaryAlignedSlotQRaw retie.pairingP
        retie.pairingQ (fkMedialVertexParity v) branch d.1.1.2
      rwa [if_pos heq] at h
  · rw [if_neg heq]
    apply (fkMedialBlackDartEquivVertexBool T).injective
    simp only [doubledAlignedBlackDart, blackDartOfStrandSlot,
      Equiv.apply_symm_apply, doubledAlignedVertex,
      doubledAlignedBranchSwap, doubledAlignedSlot]
    rw [hP, hQ]
    apply Prod.ext
    · rfl
    · have h := blackSideIndex_boundaryAlignedSlotQRaw retie.pairingP
        retie.pairingQ (fkMedialVertexParity v) branch d.1.1.2
      rwa [if_neg heq] at h


abbrev SixVertexDegreeTwoAlignedSelectedStates
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :=
  canonicalDoubledAlignedSelectedStates homega heta hdegree middle
    homegaSector hetaSector hmiddle


abbrev SixVertexDegreeTwoAlignedBoundaryOccurrence
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :=
  {dart : FKMedialBlackDart T // dart ∈
    doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)}



noncomputable def sixVertexDegreeTwoAlignedBoundaryKey
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle) :
    T.Vertex × Bool :=
  if layer then
    fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)
      (alignedBlackDartLayerSwap homega heta hdegree occurrence.1)
  else
    fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false) occurrence.1

theorem sixVertexDegreeTwoAlignedBoundaryKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoAlignedBoundaryKey homega heta hdegree middle
        homegaSector hetaSector hmiddle layer) := by
  intro first second h
  apply Subtype.ext
  cases layer
  · apply (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective
    exact h
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    apply (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective
    exact h


noncomputable def sixVertexDegreeTwoAlignedBoundaryFinKey
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
  sixVertexDegreeTwoAlignedBoundaryKey homega heta hdegree middle
    homegaSector hetaSector hmiddle layer
      ((Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i)

theorem sixVertexDegreeTwoAlignedBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle layer) :=
  (sixVertexDegreeTwoAlignedBoundaryKey_injective homega heta hdegree
    middle homegaSector hetaSector hmiddle layer).comp
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm.injective



noncomputable def sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T) : T.Vertex × Bool :=
  if layer then
    fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)
      (alignedBlackDartLayerSwap homega heta hdegree dart)
  else
    fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false) dart

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree false dart =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false) dart := by
  rfl

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree true dart =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)
        (alignedBlackDartLayerSwap homega heta hdegree dart) := by
  rfl



theorem sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart
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
        middle homegaSector hetaSector hmiddle))) :
    sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer
        ((Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i).1 := by
  cases layer <;> rfl



theorem sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) :
    (exists i, sixVertexDegreeTwoAlignedBoundaryFinKey
        homega heta hdegree middle homegaSector hetaSector hmiddle layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) <->
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      (Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart] at hi
    have hdart : occurrence.1 = dart := by
      cases layer
      · exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective hi
      · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        exact (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective hi
    rw [← hdart]
    exact occurrence.2
  · intro hdart
    let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle) occurrence
    refine ⟨i, ?_⟩
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)




theorem sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree (!layer) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle :=
    ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree middle
      homegaSector hetaSector hmiddle) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree currentLayer dart := by
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_eq_slotOfFalseDart]
    congr 1
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]



theorem sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoAlignedBoundaryFinKey_injective homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart ((sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff_dart_mem
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart).mp
      hexists)



theorem sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (x : DoubledAlignedState omega eta) :
    (exists i, sixVertexDegreeTwoAlignedBoundaryFinKey
        homega heta hdegree middle homegaSector hetaSector hmiddle layer i =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x)) ↔
      x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
        middle homegaSector hetaSector hmiddle := by
  classical
  cases layer
  · constructor
    · rintro ⟨i, hi⟩
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) occurrence.1 =
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) at hi
      have hcoordinate : fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) occurrence.1 =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)
            (doubledAlignedBlackDart homega heta hdegree false x) := by
        simpa only [doubledAlignedBlackDart,
          fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot] using hi
      have hdart : occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree false x :=
        (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)).injective
            hcoordinate
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) := by
        rw [← hdart]
        exact occurrence.2
      exact (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mp hmem
    · intro hx
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) :=
        (doubledAlignedBlackDart_mem_boundarySegments_iff
          homega heta hdegree false _ x).mpr hx
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        ⟨doubledAlignedBlackDart homega heta hdegree false x, hmem⟩
      let i := Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle) occurrence
      refine ⟨i, ?_⟩
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)
            ((Fintype.equivFin
              (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
                middle homegaSector hetaSector hmiddle)).symm i).1 = _
      rw [show (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i = occurrence by
        simp [i]]
      exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x)
  · constructor
    · rintro ⟨i, hi⟩
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
          (alignedBlackDartLayerSwap homega heta hdegree occurrence.1) =
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) at hi
      have hcoordinate : fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
          (alignedBlackDartLayerSwap homega heta hdegree occurrence.1) =
        fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
            (doubledAlignedBlackDart homega heta hdegree true x) := by
        simpa only [doubledAlignedBlackDart,
          fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot] using hi
      have hswap : alignedBlackDartLayerSwap homega heta hdegree occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree true x :=
        (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)).injective
            hcoordinate
      have hdart : occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree false x := by
        apply (alignedBlackDartLayerSwap homega heta hdegree).injective
        rw [hswap]
        exact (alignedBlackDartLayerSwap_active
          homega heta hdegree x).symm
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) := by
        rw [← hdart]
        exact occurrence.2
      exact (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mp hmem
    · intro hx
      have hmem : doubledAlignedBlackDart homega heta hdegree false x ∈
          doubledAlignedBoundarySegments homega heta hdegree false
            (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
              middle homegaSector hetaSector hmiddle) :=
        (doubledAlignedBlackDart_mem_boundarySegments_iff
          homega heta hdegree false _ x).mpr hx
      let occurrence : SixVertexDegreeTwoAlignedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle :=
        ⟨doubledAlignedBlackDart homega heta hdegree false x, hmem⟩
      let i := Fintype.equivFin
        (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle) occurrence
      refine ⟨i, ?_⟩
      change fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true)
          (alignedBlackDartLayerSwap homega heta hdegree
            ((Fintype.equivFin
              (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
                middle homegaSector hetaSector hmiddle)).symm i).1) = _
      rw [show (Fintype.equivFin
          (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
            middle homegaSector hetaSector hmiddle)).symm i = occurrence by
        simp [i]]
      rw [show occurrence.1 =
          doubledAlignedBlackDart homega heta hdegree false x by rfl,
        alignedBlackDartLayerSwap_active]
      exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x)


noncomputable def sixVertexDegreeTwoAlignedSelectedStateFinIndex
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
    Fin (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle)) :=
  Fintype.equivFin
    (SixVertexDegreeTwoAlignedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle)
    ⟨doubledAlignedBlackDart homega heta hdegree false x,
      (doubledAlignedBlackDart_mem_boundarySegments_iff
        homega heta hdegree false _ x).mpr hx⟩

@[simp] theorem sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta)
    (hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree
      middle homegaSector hetaSector hmiddle) (layer : Bool) :
    sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle layer
        (sixVertexDegreeTwoAlignedSelectedStateFinIndex homega heta hdegree
          middle homegaSector hetaSector hmiddle x hx) =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x) := by
  unfold sixVertexDegreeTwoAlignedBoundaryFinKey
    sixVertexDegreeTwoAlignedSelectedStateFinIndex
  rw [Equiv.symm_apply_apply]
  cases layer
  · change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedBlackDart homega heta hdegree false x) = _
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree false) _
  · change fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)
      (alignedBlackDartLayerSwap homega heta hdegree
        (doubledAlignedBlackDart homega heta hdegree false x)) = _
    rw [alignedBlackDartLayerSwap_active]
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree true) _



noncomputable def sixVertexDegreeTwoAlignedColoredSource
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    FKColoredLoopPairingPair T
  | false =>
      SixVertexCompatibleLoopPairing.toColored
        ⟨alignedRoutingLoopPairing homega heta hdegree false,
          alignedRoutingPairing_compatible homega heta hdegree false⟩
  | true =>
      SixVertexCompatibleLoopPairing.toColored
        ⟨alignedRoutingLoopPairing homega heta hdegree true,
          alignedRoutingPairing_compatible homega heta hdegree true⟩

@[simp] theorem sixVertexDegreeTwoAlignedColoredSource_arrows
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (layer : Bool) :
    (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree layer).arrows = if layer then eta else omega := by
  cases layer <;> exact SixVertexCompatibleLoopPairing.toColored_arrows _

theorem sixVertexDegreeTwoAlignedColoredSource_slotColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) (slot : Bool) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, v, slot) =
      (fkMedialVertexParity v ^^
        horizontalSlot
          (sixVertexLocalIncomingPattern (if layer then eta else omega) v)
          slot) := by
  cases layer <;> cases slot <;>
    simp [sixVertexDegreeTwoAlignedColoredSource,
      fkColoredLayeredSlotColor, SixVertexCompatibleLoopPairing.toColored,
      fkMedialCheckerColor, fkMedialSideVertical, horizontalSlot,
      sixVertexLocalIncomingPattern, fkMedialDartIncoming,
      fkLoopWestIncoming, fkLoopEastIncoming]


theorem sixVertexDegreeTwoAlignedColoredSource_doubledDart_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).color
        (doubledAlignedBlackDart homega heta hdegree layer x).1) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
  cases layer
  · rw [FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (false, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree false)
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree false x)))
  · rw [FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (true, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree true x)))



theorem sixVertexDegreeTwoAlignedColoredSource_falseDart_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree false).color
        (doubledAlignedBlackDart homega heta hdegree false x).1) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) := by
  rw [FKColoredLoopPairing.color_blackDart_eq_slotColor]
  exact congrArg
    (fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
    (congrArg (fun slot : T.Vertex × Bool => (false, slot))
      (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x)))



theorem sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree true).color
        (doubledAlignedBlackDart homega heta hdegree false x).1) =
      if retie.pairingP = retie.pairingQ then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree true x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
            doubledAlignedSlot homega heta hdegree true
              (doubledAlignedBranchSwap x)) := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  change ((sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree true).color
        (doubledAlignedBlackDart homega heta hdegree false x).1) =
    if retie.pairingP = retie.pairingQ then
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x)
    else
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap x))
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree x
    dsimp only at hdart
    rw [if_pos heq] at hdart
    rw [← hdart, FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (true, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree true x)))
  · rw [if_neg heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap x)
    simp only [doubledAlignedBranchSwap_fst,
      doubledAlignedBranchSwap_self] at hdart
    rw [if_neg heq] at hdart
    rw [← hdart, FKColoredLoopPairing.color_blackDart_eq_slotColor]
    exact congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
      (congrArg (fun slot : T.Vertex × Bool => (true, slot))
        (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (doubledAlignedVertex (doubledAlignedBranchSwap x),
            doubledAlignedSlot homega heta hdegree true
              (doubledAlignedBranchSwap x))))



theorem FKColoredLoopPairing.color_blackBoundaryPerm
    {T : EvenTorus} (source : FKColoredLoopPairing T)
    (dart : FKMedialBlackDart T) :
    source.color (fkMedialBlackBoundaryPerm source.pairing dart).1 =
      source.color dart.1 := by
  exact (source.color_bondMate
    (fkMedialLocalMate source.pairing dart.1)).trans
      (source.color_localMate dart.1)


theorem FKColoredLoopPairing.color_blackBoundaryPerm_pow
    {T : EvenTorus} (source : FKColoredLoopPairing T)
    (dart : FKMedialBlackDart T) (k : Nat) :
    source.color ((fkMedialBlackBoundaryPerm source.pairing ^ k) dart).1 =
      source.color dart.1 := by
  induction k generalizing dart with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (ih (fkMedialBlackBoundaryPerm source.pairing dart)).trans
        (source.color_blackBoundaryPerm dart)



theorem sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) (k : Nat) :
    ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer).color
        ((alignedBoundaryPerm homega heta hdegree layer ^ k)
          (doubledAlignedBlackDart homega heta hdegree layer x)).1) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
  have hpower := FKColoredLoopPairing.color_blackBoundaryPerm_pow
    (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree layer)
    (doubledAlignedBlackDart homega heta hdegree layer x) k
  have hpairing :
      (sixVertexDegreeTwoAlignedColoredSource
        homega heta hdegree layer).pairing =
        alignedRoutingLoopPairing homega heta hdegree layer := by
    cases layer <;> rfl
  rw [hpairing] at hpower
  change ((sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree layer).color
        ((alignedBoundaryPerm homega heta hdegree layer ^ k)
          (doubledAlignedBlackDart homega heta hdegree layer x)).1) =
    (sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree layer).color
        (doubledAlignedBlackDart homega heta hdegree layer x).1 at hpower
  rw [hpower, FKColoredLoopPairing.color_blackDart_eq_slotColor]
  rw [hpairing]
  exact congrArg
    (fkColoredLayeredSlotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
    (congrArg (fun slot : T.Vertex × Bool => (layer, slot))
      (fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x)))



theorem sixVertexDegreeTwoAlignedColoredSource_boundarySegment_slotColor
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta)
    (dart : FKMedialBlackDart T) (k : Nat)
    (hk : k < finiteFirstReturnTime
      (alignedBoundaryPerm homega heta hdegree false)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv homega heta hdegree false x))
    (hpow : (alignedBoundaryPerm homega heta hdegree false ^ k)
      (doubledAlignedBlackDart homega heta hdegree false x) = dart) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree layer x) := by
  classical
  cases layer
  · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false,
      ← hpow]
    let powered := (alignedBoundaryPerm homega heta hdegree false ^ k)
      (doubledAlignedBlackDart homega heta hdegree false x)
    have hcoordinate := FKColoredLoopPairing.color_blackDart_eq_slotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      false powered
    exact hcoordinate.symm.trans
      (sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
        homega heta hdegree false x k)
  · have hswap := alignedBlackDartLayerSwap_power
      homega heta hdegree x k hk
    rw [hpow] at hswap
    rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
      hswap]
    let powered := (alignedBoundaryPerm homega heta hdegree true ^ k)
      (doubledAlignedBlackDart homega heta hdegree true x)
    have hcoordinate := FKColoredLoopPairing.color_blackDart_eq_slotColor
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      true powered
    exact hcoordinate.symm.trans
      (sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
        homega heta hdegree true x k)



theorem sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_false
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false,
          doubledAlignedVertex
            (doubledAlignedFirstReturnPerm homega heta hdegree x),
          doubledAlignedSlot homega heta hdegree false
            (doubledAlignedFirstReturnPerm homega heta hdegree x)) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let k := finiteFirstReturnTime
    (alignedBoundaryPerm homega heta hdegree false)
    (activeBlackDart (omega := omega) (eta := eta))
    (doubledAlignedBlackDartEquiv homega heta hdegree false x)
  have harrival := congrArg Subtype.val
    (doubledAlignedFirstReturnPerm_false_arrival
      homega heta hdegree x)
  change doubledAlignedBlackDart homega heta hdegree false y =
    (alignedBoundaryPerm homega heta hdegree false ^ k)
      (doubledAlignedBlackDart homega heta hdegree false x) at harrival
  have hpower :=
    sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
      homega heta hdegree false x k
  rw [← harrival] at hpower
  have hy := sixVertexDegreeTwoAlignedColoredSource_falseDart_color
    homega heta hdegree y
  exact hpower.symm.trans hy




theorem sixVertexDegreeTwoAlignedColoredSource_firstReturn_color_true
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let y := doubledAlignedFirstReturnPerm homega heta hdegree x
    let retie := orientedDartAlignedRetie homega heta hdegree y.1
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) =
      if retie.pairingP = retie.pairingQ then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex y,
            doubledAlignedSlot homega heta hdegree true y)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (true, doubledAlignedVertex (doubledAlignedBranchSwap y),
            doubledAlignedSlot homega heta hdegree true
              (doubledAlignedBranchSwap y)) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  let k := finiteFirstReturnTime
    (alignedBoundaryPerm homega heta hdegree true)
    (activeBlackDart (omega := omega) (eta := eta))
    (doubledAlignedBlackDartEquiv homega heta hdegree true x)
  have harrival := doubledAlignedFirstReturnPerm_true_common_arrival
    homega heta hdegree x
  change (alignedBoundaryPerm homega heta hdegree true ^ k)
      (doubledAlignedBlackDart homega heta hdegree true x) =
    doubledAlignedBlackDart homega heta hdegree false y at harrival
  have hpower :=
    sixVertexDegreeTwoAlignedColoredSource_boundaryPower_color
      homega heta hdegree true x k
  rw [harrival] at hpower
  have hy := sixVertexDegreeTwoAlignedColoredSource_falseDart_true_color
    homega heta hdegree y
  change ((sixVertexDegreeTwoAlignedColoredSource
      homega heta hdegree true).color
        (doubledAlignedBlackDart homega heta hdegree false y).1) =
    (if retie.pairingP = retie.pairingQ then
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex y,
          doubledAlignedSlot homega heta hdegree true y)
    else
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap y),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap y))) at hy
  exact hpower.symm.trans hy




theorem sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree false dart) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree true dart) := by
  have hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega dart.1.1)
      (sixVertexLocalIncomingPattern eta dart.1.1)).card = 0 := by
    rcases hdegree dart.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hinactive htwo)
  have hpatterns : sixVertexLocalIncomingPattern eta dart.1.1 =
      sixVertexLocalIncomingPattern omega dart.1.1 :=
    (localIncomingPattern_eq_of_disagreement_card_zero _ _ hzero).symm
  have hpairing := alignedRoutingPairing_eq_layers_at_inactive
    homega heta hdegree dart.1.1 hzero
  change alignedRoutingLoopPairing homega heta hdegree false dart.1.1 =
    alignedRoutingLoopPairing homega heta hdegree true dart.1.1 at hpairing
  rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false,
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
    alignedBlackDartLayerSwap_inactive homega heta hdegree dart hinactive,
    sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [Bool.false_eq_true, if_false, if_true,
    fkColoredBlackDartStrandSlotEquiv_apply,
    fkColoredBlackDartStrandSlot]
  rw [hpatterns, hpairing]




theorem sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (false, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree false x) !=
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x)) =
      if x.2 then
        (retie.pairingP != retie.pairingQ) &&
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2)
      else
        (retie.pairingP == retie.pairingQ) ||
          (fkMedialVertexParity (doubledAlignedVertex x) !=
            sideVertical x.1.1.1.2) := by
  rcases x with ⟨d, branch⟩
  let p := sixVertexLocalIncomingPattern omega d.1.1.1
  let q := sixVertexLocalIncomingPattern eta d.1.1.1
  let retie := orientedDartAlignedRetie homega heta hdegree d
  rw [sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [Bool.false_eq_true, if_false, if_true]
  change
    ((fkMedialVertexParity d.1.1.1 ^^
          horizontalSlot p
            (if branch then !strandSlot retie.pairingP d.1.1.2
              else strandSlot retie.pairingP d.1.1.2)) !=
      (fkMedialVertexParity d.1.1.1 ^^
          horizontalSlot q
            (if branch then
              !boundaryAlignedSlotQRaw (fkMedialVertexParity d.1.1.1)
                retie.pairingP retie.pairingQ d.1.1.2
            else boundaryAlignedSlotQRaw
              (fkMedialVertexParity d.1.1.1)
                retie.pairingP retie.pairingQ d.1.1.2))) =
      if branch then
        (retie.pairingP != retie.pairingQ) &&
          (fkMedialVertexParity d.1.1.1 != sideVertical d.1.1.2)
      else
        (retie.pairingP == retie.pairingQ) ||
          (fkMedialVertexParity d.1.1.1 != sideVertical d.1.1.2)
  cases branch
  · exact boundaryAlignedSlotColor_bne p q retie.pairingP retie.pairingQ
      (fkMedialVertexParity d.1.1.1) d.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
      (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
      retie.compatibleP retie.compatibleQ
      (by
        have hd := sixVertexDisagreementDart_side_mem d.1
        rw [mem_sixVertexLocalDisagreementSides] at hd
        exact bne_iff_ne.mpr hd)
      retie.partnerDisagrees
  · simpa using boundaryAlignedComplementSlotColor_bne p q
      retie.pairingP retie.pairingQ
      (fkMedialVertexParity d.1.1.1) d.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
      (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
      retie.compatibleP retie.compatibleQ
      (by
        have hd := sixVertexDisagreementDart_side_mem d.1
        rw [mem_sixVertexLocalDisagreementSides] at hd
        exact bne_iff_ne.mpr hd)
      retie.partnerDisagrees




theorem sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (hne : (orientedDartAlignedRetie
      homega heta hdegree x.1).pairingP !=
        (orientedDartAlignedRetie
          homega heta hdegree x.1).pairingQ) :
    (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) !=
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap x))) = true := by
  rcases x with ⟨d, branch⟩
  let p := sixVertexLocalIncomingPattern omega d.1.1.1
  let q := sixVertexLocalIncomingPattern eta d.1.1.1
  let retie := orientedDartAlignedRetie homega heta hdegree d
  rw [sixVertexDegreeTwoAlignedColoredSource_slotColor,
    sixVertexDegreeTwoAlignedColoredSource_slotColor]
  simp only [if_true,
    doubledAlignedVertex, doubledAlignedBranchSwap,
    doubledAlignedSlot, Bool.not_eq_eq_eq_not]
  simp only [orientedDartBoundaryAlignedSlot, boundaryAlignedSlotQ, if_true]
  have hlocal := boundaryAlignedSlotQRaw_complement_color_bne_of_pairing_ne
    p q retie.pairingP retie.pairingQ
    (fkMedialVertexParity d.1.1.1) d.1.1.2
    (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
    (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
    (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
    retie.compatibleP retie.compatibleQ
    (by
      have hd := sixVertexDisagreementDart_side_mem d.1
      rw [mem_sixVertexLocalDisagreementSides] at hd
      exact bne_iff_ne.mpr hd)
    retie.partnerDisagrees hne
  cases branch
  · simpa [p, q, retie] using hlocal
  · simpa [p, q, retie, bne_comm] using hlocal





theorem sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne_of_false_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta)
    (hfalse :
      fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree false x) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (false, doubledAlignedVertex (doubledAlignedBranchSwap x),
            doubledAlignedSlot homega heta hdegree false
              (doubledAlignedBranchSwap x))) :
    (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex x,
          doubledAlignedSlot homega heta hdegree true x) !=
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
          doubledAlignedSlot homega heta hdegree true
            (doubledAlignedBranchSwap x))) = true := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  by_cases hpairing : retie.pairingP = retie.pairingQ
  · have hcrossX := sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne
      homega heta hdegree x
    have hcrossSwap := sixVertexDegreeTwoAlignedColoredSource_activeSlot_bne
      homega heta hdegree (doubledAlignedBranchSwap x)
    have hswapBranch : (doubledAlignedBranchSwap x).2 = !x.2 := rfl
    by_cases hbranch : x.2 = true
    · have hsameX :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree false x) =
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree true x) := by
        simpa [retie, hpairing, hbranch] using hcrossX
      have hneSwap :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree false
                  (doubledAlignedBranchSwap x)) ≠
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree true
                  (doubledAlignedBranchSwap x)) := by
        simpa [retie, hpairing, hbranch, hswapBranch] using hcrossSwap
      apply bne_iff_ne.mpr
      intro heq
      apply hneSwap
      exact hfalse.symm.trans (hsameX.trans heq)
    · have hneX :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree false x) ≠
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex x,
                doubledAlignedSlot homega heta hdegree true x) := by
        simpa [retie, hpairing, hbranch] using hcrossX
      have hsameSwap :
          fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (false, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree false
                  (doubledAlignedBranchSwap x)) =
            fkColoredLayeredSlotColor
              (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
              (true, doubledAlignedVertex (doubledAlignedBranchSwap x),
                doubledAlignedSlot homega heta hdegree true
                  (doubledAlignedBranchSwap x)) := by
        simpa [retie, hpairing, hbranch, hswapBranch] using hcrossSwap
      apply bne_iff_ne.mpr
      intro heq
      apply hneX
      exact hfalse.trans (hsameSwap.trans heq.symm)
  · exact sixVertexDegreeTwoAlignedColoredSource_true_branchSwap_bne
      homega heta hdegree x (bne_iff_ne.mpr hpairing)

theorem sixVertexDegreeTwoAlignedTransportedColor_active
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
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if _hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates
          homega heta hdegree middle homegaSector hetaSector hmiddle then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  classical
  by_cases hx : x ∈ SixVertexDegreeTwoAlignedSelectedStates
      homega heta hdegree middle homegaSector hetaSector hmiddle
  · rw [dif_pos hx]
    let i := sixVertexDegreeTwoAlignedSelectedStateFinIndex
      homega heta hdegree middle homegaSector hetaSector hmiddle x hx
    rw [← sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState
        homega heta hdegree middle homegaSector hetaSector hmiddle x hx layer]
    rw [fkIndexedOccurrenceSlotEquiv_apply_key]
    rw [sixVertexDegreeTwoAlignedBoundaryFinKey_selectedState]
  · rw [dif_neg hx]
    apply congrArg
      (fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree))
    apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
    intro hexists
    apply hx
    exact (sixVertexDegreeTwoAlignedBoundaryFinKey_exists_iff
      homega heta hdegree middle homegaSector hetaSector hmiddle layer x).mp
        hexists


abbrev SixVertexDegreeTwoAlignedOrbitCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :=
  CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle



def sixVertexRetieAtTransitionVertices
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) : FKMedialLoopPairing T :=
  if first = second then fkMedialTogglePairingAt pairing first
  else fkMedialTogglePairingAt
    (fkMedialTogglePairingAt pairing first) second




noncomputable def sixVertexDegreeTwoAlignedTargetPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) : FKMedialLoopPairing T := by
  let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
    homegaSector hetaSector hmiddle
  by_cases hleft : cut.cutLeft = []
  · exact alignedRoutingLoopPairing homega heta hdegree layer
  · by_cases hright : cut.cutRight = []
    · exact alignedRoutingLoopPairing homega heta hdegree layer
    · exact sixVertexRetieAtTransitionVertices
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (doubledAlignedVertex (cut.cutRight.head hright))
        (doubledAlignedVertex (cut.cutLeft.head hleft))

theorem sixVertexDegreeTwoAlignedTargetPairing_of_left_empty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft = [])
    (layer : Bool) :
    sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  simp [sixVertexDegreeTwoAlignedTargetPairing, hleft]

theorem sixVertexDegreeTwoAlignedTargetPairing_of_right_empty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight = [])
    (layer : Bool) :
    sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
        homegaSector hetaSector hmiddle layer =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  simp [sixVertexDegreeTwoAlignedTargetPairing, hright]

end

end StatMech.FrontierD
