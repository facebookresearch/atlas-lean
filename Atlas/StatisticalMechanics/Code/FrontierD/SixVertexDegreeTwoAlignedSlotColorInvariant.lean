/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexTransitionRetieExact
import Code.FrontierD.SixVertexRoutedKeySlotColorInvariant
import Code.FrontierD.SixVertexDegreeTwoCanonicalUnitRoute










namespace StatMech.FrontierD

noncomputable section

local instance sixVertexDegreeTwoAlignedSlotColorInvariantActiveDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _




noncomputable def sixVertexDegreeTwoBranchClosedUnitPrefix
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    List (DoubledAlignedState omega eta) :=
  (sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
    homegaSector hetaSector hmiddle).flatMap fun dart =>
      [(dart, false), (dart, true)]

@[simp] theorem mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle ↔
      x.1 ∈ sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle := by
  rcases x with ⟨dart, branch⟩
  cases branch <;>
    simp [sixVertexDegreeTwoBranchClosedUnitPrefix]

theorem sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap x ∈
        sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle ↔
      x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle := by
  rw [mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff,
    mem_sixVertexDegreeTwoBranchClosedUnitPrefix_iff]
  rfl

theorem sixVertexDegreeTwoBranchClosedUnitPrefix_charge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) :
    ((sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
      homegaSector hetaSector hmiddle).map
        (doubledAlignedCharge hdegree)).sum = 1 := by
  rw [sixVertexDegreeTwoBranchClosedUnitPrefix]
  simp only [List.map_flatMap]
  change (((sixVertexDegreeTwoCanonicalUnitPrefix homega heta hdegree middle
    homegaSector hetaSector hmiddle).flatMap fun dart =>
      [sixVertexDegreeTwoStrandStepSeamSign hdegree dart, 0]).sum) = 1
  have hcollapse (darts :
      List (SixVertexOrientedDisagreementDart omega eta)) :
      (darts.flatMap fun dart =>
          [sixVertexDegreeTwoStrandStepSeamSign hdegree dart, 0]).sum =
        (darts.map
          (sixVertexDegreeTwoStrandStepSeamSign hdegree)).sum := by
    induction darts with
    | nil => rfl
    | cons dart darts ih => simp [ih]
  rw [hcollapse]
  exact sixVertexDegreeTwoCanonicalUnitPrefix_sum
    homega heta hdegree middle homegaSector hetaSector hmiddle



abbrev SixVertexDegreeTwoBranchClosedBoundaryOccurrence
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
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)}



noncomputable def sixVertexDegreeTwoBranchClosedBoundaryFinKey
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
  sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer
    ((Fintype.equivFin
      (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle)).symm i).1

theorem sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    Function.Injective
      (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
        middle homegaSector hetaSector hmiddle layer) := by
  intro first second heq
  apply (Fintype.equivFin
    (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle)).symm.injective
  apply Subtype.ext
  unfold sixVertexDegreeTwoBranchClosedBoundaryFinKey at heq
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).injective heq
  · apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree true)).injective heq

theorem sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T) :
    (exists i, sixVertexDegreeTwoBranchClosedBoundaryFinKey
        homega heta hdegree middle homegaSector hetaSector hmiddle layer i =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    let occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      (Fintype.equivFin
        (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
          middle homegaSector hetaSector hmiddle)).symm i
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
    let occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle :=
      ⟨dart, hdart⟩
    let i := Fintype.equivFin
      (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
        middle homegaSector hetaSector hmiddle) occurrence
    refine ⟨i, ?_⟩
    unfold sixVertexDegreeTwoBranchClosedBoundaryFinKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)

theorem sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
          homega heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree (!layer) dart) := by
  classical
  let occurrence : SixVertexDegreeTwoBranchClosedBoundaryOccurrence
      homega heta hdegree middle homegaSector hetaSector hmiddle :=
    ⟨dart, hdart⟩
  let i := Fintype.equivFin
    (SixVertexDegreeTwoBranchClosedBoundaryOccurrence homega heta hdegree
      middle homegaSector hetaSector hmiddle) occurrence
  have hkey (currentLayer : Bool) :
      sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle
          homegaSector hetaSector hmiddle currentLayer i =
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree currentLayer dart := by
    unfold sixVertexDegreeTwoBranchClosedBoundaryFinKey
    congr 2
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ occurrence)
  rw [← hkey layer, fkIndexedOccurrenceSlotEquiv_apply_key, hkey]

theorem sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T)
    (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)) :
    fkIndexedOccurrenceSlotEquiv
        (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
          homega heta hdegree middle homegaSector hetaSector hmiddle))
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
          middle homegaSector hetaSector hmiddle)
        (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
          homega heta hdegree middle homegaSector hetaSector hmiddle)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) := by
  apply fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
  intro hexists
  exact hdart ((sixVertexDegreeTwoBranchClosedBoundaryFinKey_exists_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle layer dart).mp
      hexists)



theorem sixVertexDegreeTwoBranchClosedBoundarySegments_branchSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree false
        (doubledAlignedBranchSwap x) ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) ↔
      doubledAlignedBlackDart homega heta hdegree false x ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) := by
  rw [doubledAlignedBlackDart_mem_boundarySegments_iff,
    doubledAlignedBlackDart_mem_boundarySegments_iff]
  exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle x



noncomputable def sixVertexDegreeTwoBranchClosedSelected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) : Bool :=
  decide (x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree
    middle homegaSector hetaSector hmiddle)

@[simp] theorem sixVertexDegreeTwoBranchClosedSelected_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (doubledAlignedBranchSwap x) =
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle x := by
  unfold sixVertexDegreeTwoBranchClosedSelected
  apply Bool.decide_congr
  exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
    homega heta hdegree middle homegaSector hetaSector hmiddle x



noncomputable def sixVertexDegreeTwoBranchClosedTransitionVertex
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
    let sigma := doubledAlignedFirstReturnPerm homega heta hdegree
    (sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (d, false) !=
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (sigma.symm (d, false))) ||
    (sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (d, true) !=
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (sigma.symm (d, true)))
  else false



noncomputable def sixVertexDegreeTwoBranchClosedInternalMismatchVertex
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
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle (d, false) &&
      ((orientedDartAlignedRetie homega heta hdegree d).pairingP !=
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ)
  else false



noncomputable def sixVertexDegreeTwoBranchClosedExpandedRetieMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (_layer : Bool) (v : T.Vertex) : Bool :=
  sixVertexDegreeTwoBranchClosedTransitionVertex homega heta hdegree middle
      homegaSector hetaSector hmiddle v ||
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex
      homega heta hdegree middle homegaSector hetaSector hmiddle v

def fkMedialTogglePairingMask {T : EvenTorus}
    (pairing : FKMedialLoopPairing T) (mask : T.Vertex -> Bool) :
    FKMedialLoopPairing T := fun v => if mask v then !pairing v else pairing v



theorem fkMedialBlackDartSwap_self_vertex {T : EvenTorus}
    (dart : FKMedialBlackDart T) :
    (fkMedialBlackDartSwap dart.1.1 dart).1.1 = dart.1.1 := by
  let pairing : FKMedialLoopPairing T := fun _ => false
  have hcoordinate := fkColoredBlackDartStrandSlot_blackSwap
    pairing dart.1.1 dart
  have hfst := congrArg Prod.fst hcoordinate
  change (fkMedialBlackDartSwap dart.1.1 dart).1.1 =
    (fkColoredVertexStrandSlotSwap dart.1.1
      (fkColoredBlackDartStrandSlotEquiv pairing dart)).1 at hfst
  have hswapFst : (fkColoredVertexStrandSlotSwap dart.1.1
      (fkColoredBlackDartStrandSlotEquiv pairing dart)).1 =
      (fkColoredBlackDartStrandSlotEquiv pairing dart).1 := by
    rcases dart with ⟨⟨v, side⟩, hdart⟩
    cases hv : fkMedialVertexParity v <;> cases side <;>
      simp [fkColoredVertexStrandSlotSwap,
        fkColoredBlackDartStrandSlotEquiv_apply,
        fkColoredBlackDartStrandSlot, fkColoredSideSlot,
        fkMedialCheckerColor, fkMedialSideVertical, pairing, hv] at hdart ⊢
  rw [hswapFst] at hfst
  exact hfst

def fkMedialBlackDartMaskSwap {T : EvenTorus}
    (mask : T.Vertex -> Bool) : Equiv.Perm (FKMedialBlackDart T) where
  toFun dart := if mask dart.1.1 then
    fkMedialBlackDartSwap dart.1.1 dart else dart
  invFun dart := if mask dart.1.1 then
    fkMedialBlackDartSwap dart.1.1 dart else dart
  left_inv dart := by
    by_cases hmask : mask dart.1.1
    · simp only [hmask, if_true]
      rw [fkMedialBlackDartSwap_self_vertex, hmask]
      simp [fkMedialBlackDartSwap]
    · simp [hmask]
  right_inv dart := by
    by_cases hmask : mask dart.1.1
    · simp only [hmask, if_true]
      rw [fkMedialBlackDartSwap_self_vertex, hmask]
      simp [fkMedialBlackDartSwap]
    · simp [hmask]



def fkColoredParityMaskStrandSlotSwap {T : EvenTorus}
    (mask : T.Vertex -> Bool) (parity : Bool) :
    Equiv.Perm (T.Vertex × Bool) where
  toFun slot :=
    if mask slot.1 && (fkMedialVertexParity slot.1 == parity) then
      (slot.1, !slot.2)
    else slot
  invFun slot :=
    if mask slot.1 && (fkMedialVertexParity slot.1 == parity) then
      (slot.1, !slot.2)
    else slot
  left_inv slot := by
    rcases slot with ⟨v, side⟩
    cases h : mask v && (fkMedialVertexParity v == parity) <;>
      cases side <;> simp [h]
  right_inv slot := by
    rcases slot with ⟨v, side⟩
    cases h : mask v && (fkMedialVertexParity v == parity) <;>
      cases side <;> simp [h]

@[simp] theorem fkColoredParityMaskStrandSlotSwap_self
    {T : EvenTorus} (mask : T.Vertex -> Bool) (parity : Bool)
    (slot : T.Vertex × Bool) :
    fkColoredParityMaskStrandSlotSwap mask parity
        (fkColoredParityMaskStrandSlotSwap mask parity slot) = slot := by
  rcases slot with ⟨v, side⟩
  cases hmask : mask v <;> cases hv : fkMedialVertexParity v <;>
    cases parity <;> cases side <;>
    simp [fkColoredParityMaskStrandSlotSwap, hmask, hv]

theorem fkColoredParityMaskStrandSlotSwap_apply_of_true
    {T : EvenTorus} (mask : T.Vertex -> Bool) (parity : Bool)
    (slot : T.Vertex × Bool)
    (hselected : (mask slot.1 &&
      (fkMedialVertexParity slot.1 == parity)) = true) :
    fkColoredParityMaskStrandSlotSwap mask parity slot =
      fkColoredVertexStrandSlotSwap slot.1 slot := by
  rcases slot with ⟨v, side⟩
  cases hmask : mask v <;> cases hv : fkMedialVertexParity v <;>
    cases parity <;> cases side <;>
    simp [fkColoredParityMaskStrandSlotSwap,
      fkColoredVertexStrandSlotSwap, hmask, hv] at hselected ⊢

theorem fkColoredParityMaskStrandSlotSwap_apply_of_false
    {T : EvenTorus} (mask : T.Vertex -> Bool) (parity : Bool)
    (slot : T.Vertex × Bool)
    (hunselected : (mask slot.1 &&
      (fkMedialVertexParity slot.1 == parity)) = false) :
    fkColoredParityMaskStrandSlotSwap mask parity slot = slot := by
  rcases slot with ⟨v, side⟩
  cases hmask : mask v <;> cases hv : fkMedialVertexParity v <;>
    cases parity <;> cases side <;>
    simp [fkColoredParityMaskStrandSlotSwap, hmask, hv] at hunselected ⊢



theorem fkMedialBlackBoundaryPerm_togglePairingMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkMedialBlackBoundaryPerm (fkMedialTogglePairingMask pairing mask) =
      fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartMaskSwap mask := by
  apply Equiv.ext
  intro dart
  apply Subtype.ext
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases hmask : mask v <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;> cases side <;>
    simp [fkMedialBlackBoundaryPerm_val, fkMedialTogglePairingMask,
      fkMedialBlackDartMaskSwap, fkMedialBlackDartSwap,
      fkMedialBlackDart0, fkMedialBlackDart1, fkMedialCheckerColor,
      fkMedialSideVertical, fkMedialLocalMate, Equiv.Perm.mul_apply,
      hmask, hp, hv] at hdart ⊢



theorem fkColoredBlackDartStrandSlotEquiv_togglePairingMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkColoredBlackDartStrandSlotEquiv
        (fkMedialTogglePairingMask pairing mask) =
      (fkColoredBlackDartStrandSlotEquiv pairing).trans
        (fkColoredParityMaskStrandSlotSwap mask true) := by
  apply Equiv.ext
  intro dart
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases hmask : mask v <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;> cases side <;>
    simp [fkColoredBlackDartStrandSlotEquiv_apply,
      fkColoredBlackDartStrandSlot, fkMedialTogglePairingMask,
      fkColoredParityMaskStrandSlotSwap, fkColoredSideSlot,
      fkMedialCheckerColor, fkMedialSideVertical, hmask, hp, hv] at hdart ⊢



theorem fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) (dart : FKMedialBlackDart T) :
    fkColoredBlackDartStrandSlotEquiv pairing
        (fkMedialBlackDartMaskSwap mask dart) =
      fkColoredParityMaskStrandSlotSwap mask false
        (fkColoredParityMaskStrandSlotSwap mask true
          (fkColoredBlackDartStrandSlotEquiv pairing dart)) := by
  rcases dart with ⟨⟨v, side⟩, hdart⟩
  cases hmask : mask v <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;> cases side <;>
    simp [fkMedialBlackDartMaskSwap, fkMedialBlackDartSwap,
      fkMedialBlackDart0, fkMedialBlackDart1,
      fkColoredBlackDartStrandSlotEquiv_apply,
      fkColoredBlackDartStrandSlot, fkColoredParityMaskStrandSlotSwap,
      fkColoredSideSlot, fkMedialCheckerColor, fkMedialSideVertical,
      hmask, hp, hv] at hdart ⊢



theorem fkColoredStrandSlotBoundaryPerm_togglePairingMask
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkColoredStrandSlotBoundaryPerm
        (fkMedialTogglePairingMask pairing mask) =
      (fkColoredParityMaskStrandSlotSwap mask false).trans
        ((fkColoredStrandSlotBoundaryPerm pairing).trans
          (fkColoredParityMaskStrandSlotSwap mask true)) := by
  let coordinate := fkColoredBlackDartStrandSlotEquiv pairing
  let whiteSwap := fkColoredParityMaskStrandSlotSwap mask false
  let blackSwap := fkColoredParityMaskStrandSlotSwap mask true
  have htargetCoordinate :=
    fkColoredBlackDartStrandSlotEquiv_togglePairingMask pairing mask
  have htargetBoundary := fkMedialBlackBoundaryPerm_togglePairingMask
    pairing mask
  apply Equiv.ext
  intro slot
  have hinput : fkMedialBlackDartMaskSwap mask
      (coordinate.symm (blackSwap slot)) =
      coordinate.symm (whiteSwap slot) := by
    apply coordinate.injective
    rw [fkColoredBlackDartStrandSlotEquiv_blackDartMaskSwap]
    simp [coordinate, whiteSwap, blackSwap]
  simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply]
  rw [htargetCoordinate, htargetBoundary]
  simp only [Equiv.trans_apply, Equiv.Perm.mul_apply]
  rw [show ((coordinate.trans blackSwap).symm slot) =
      coordinate.symm (blackSwap slot) by
    change coordinate.symm (blackSwap.symm slot) = _
    rw [show blackSwap.symm slot = blackSwap slot by rfl]]
  rw [hinput]

@[simp] theorem fkMedialTogglePairingMask_self
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (mask : T.Vertex -> Bool) :
    fkMedialTogglePairingMask
        (fkMedialTogglePairingMask pairing mask) mask = pairing := by
  funext v
  cases hmask : mask v <;> simp [fkMedialTogglePairingMask, hmask]



noncomputable def sixVertexDegreeTwoBranchClosedExpandedTargetPairing
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
    (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
      middle homegaSector hetaSector hmiddle layer)

theorem sixVertexDegreeTwoBranchClosedExpandedTargetBoundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta
          hdegree middle homegaSector hetaSector hmiddle layer) =
      (fkColoredParityMaskStrandSlotSwap
        (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) false).trans
        ((fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer)).trans
        (fkColoredParityMaskStrandSlotSwap
          (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
            middle homegaSector hetaSector hmiddle layer) true)) := by
  exact fkColoredStrandSlotBoundaryPerm_togglePairingMask _ _

@[simp] theorem sixVertexDegreeTwoBranchClosedExpandedTargetPairing_recover
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) :
    fkMedialTogglePairingMask
        (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta
          hdegree middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
          middle homegaSector hetaSector hmiddle layer) =
      alignedRoutingLoopPairing homega heta hdegree layer := by
  exact fkMedialTogglePairingMask_self _ _

@[simp] theorem sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive
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
    sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree middle
      homegaSector hetaSector hmiddle layer v = false := by
  have hnot : Not ((sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) := by omega
  simp [sixVertexDegreeTwoBranchClosedExpandedRetieMask,
    sixVertexDegreeTwoBranchClosedTransitionVertex,
    sixVertexDegreeTwoBranchClosedInternalMismatchVertex, hnot]

theorem sixVertexDegreeTwoBranchClosedExpandedTargetPairing_inactive
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
    sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer v =
      alignedRoutingLoopPairing homega heta hdegree layer v := by
  simp [sixVertexDegreeTwoBranchClosedExpandedTargetPairing,
    fkMedialTogglePairingMask,
    sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer v hzero]

theorem sixVertexDegreeTwoBranchClosedExpandedTargetPairing_active
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
    let transition := sixVertexDegreeTwoBranchClosedTransitionVertex
      homega heta hdegree middle homegaSector hetaSector hmiddle v
    let internal := sixVertexDegreeTwoBranchClosedInternalMismatchVertex
      homega heta hdegree middle homegaSector hetaSector hmiddle v
    sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle layer v =
      if transition || internal then
        !(if layer then
          (orientedDartAlignedRetie homega heta hdegree d).pairingQ
        else (orientedDartAlignedRetie homega heta hdegree d).pairingP)
      else if layer then
        (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP := by
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
  have hsource := alignedRoutingPairing_eq_at_active
    homega heta hdegree layer v hactive
  change alignedRoutingLoopPairing homega heta hdegree layer v =
    (if layer then (orientedDartAlignedRetie homega heta hdegree d).pairingQ
      else (orientedDartAlignedRetie homega heta hdegree d).pairingP) at hsource
  rw [sixVertexDegreeTwoBranchClosedExpandedTargetPairing,
    fkMedialTogglePairingMask, hsource]
  rfl

theorem sixVertexDegreeTwoBranchClosedTransportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments
          homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments
      homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hdart,
      sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]
  · rw [dif_neg hdart,
      sixVertexDegreeTwoBranchClosedOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer
        (doubledAlignedBlackDart homega heta hdegree false x) =
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x) := by
  cases layer
  · exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree false) _
  · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
      alignedBlackDartLayerSwap_active]
    exact fkColoredBlackDartStrandSlotEquiv_blackDartOfStrandSlot
      (alignedRoutingLoopPairing homega heta hdegree true) _



theorem sixVertexDegreeTwoBranchClosedTransportedColor_active
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
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x)) =
      if _hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta
          hdegree middle homegaSector hetaSector hmiddle then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree (!layer) x)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, doubledAlignedVertex x,
            doubledAlignedSlot homega heta hdegree layer x) := by
  rw [← sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_active
      homega heta hdegree layer x,
    sixVertexDegreeTwoBranchClosedTransportedColor_dart]
  have hmem := doubledAlignedBlackDart_mem_boundarySegments_iff
    homega heta hdegree false
      (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
        homegaSector hetaSector hmiddle) x
  by_cases hx : x ∈ sixVertexDegreeTwoBranchClosedUnitPrefix homega heta
      hdegree middle homegaSector hetaSector hmiddle
  · rw [dif_pos (hmem.mpr hx), dif_pos hx]
    simp
  · rw [dif_neg (fun hdart => hx (hmem.mp hdart)), dif_neg hx]

theorem sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive
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
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) := by
  classical
  rw [sixVertexDegreeTwoBranchClosedTransportedColor_dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl




theorem sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    fkColoredStrandSlotBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (if layer then
          (alignedBlackDartLayerSwap homega heta hdegree).symm
            (alignedBoundaryPerm homega heta hdegree false dart)
        else alignedBoundaryPerm homega heta hdegree false dart) := by
  cases layer
  · simp only [Bool.false_eq_true, if_false,
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false]
    change (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false))
          ((alignedBoundaryPerm homega heta hdegree false)
            ((fkColoredBlackDartStrandSlotEquiv
              (alignedRoutingLoopPairing homega heta hdegree false)).symm
              ((fkColoredBlackDartStrandSlotEquiv
                (alignedRoutingLoopPairing homega heta hdegree false)) dart))) =
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false))
          ((alignedBoundaryPerm homega heta hdegree false) dart)
    rw [Equiv.symm_apply_apply]
  · let swap := alignedBlackDartLayerSwap homega heta hdegree
    let next := alignedBoundaryPerm homega heta hdegree false dart
    have hstep : alignedBoundaryPerm homega heta hdegree true (swap dart) =
        next := (alignedBoundaryPerm_false_eq_true_layerSwap
          homega heta hdegree dart).symm
    simp only [if_true,
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
    change fkColoredStrandSlotBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true)
        (fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) (swap dart)) =
      fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)
        (swap (swap.symm next))
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    exact congrArg
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)) hstep




noncomputable def sixVertexDegreeTwoAlignedTrueFirstReturnState
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  if retie.pairingP = retie.pairingQ then y
  else doubledAlignedBranchSwap y

theorem sixVertexDegreeTwoAlignedTrueFirstReturn_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree true x) =
      doubledAlignedBlackDartEquiv homega heta hdegree true
        (sixVertexDegreeTwoAlignedTrueFirstReturnState
          homega heta hdegree x) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  have hcommon := doubledAlignedFirstReturnPerm_true_common_arrival
    homega heta hdegree x
  apply Subtype.ext
  unfold sixVertexDegreeTwoAlignedTrueFirstReturnState
  change (finiteFirstReturn
      (alignedBoundaryPerm homega heta hdegree true)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv homega heta hdegree true x)).1 =
    (doubledAlignedBlackDartEquiv homega heta hdegree true
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y)).1
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree y
    dsimp only at hdart
    rw [if_pos heq] at hdart
    exact hcommon.trans hdart.symm
  · rw [if_neg heq]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap y)
    simp only [doubledAlignedBranchSwap_fst,
      doubledAlignedBranchSwap_self] at hdart
    rw [if_neg heq] at hdart
    exact hcommon.trans hdart.symm

theorem sixVertexDegreeTwoBranchClosedSelected_trueFirstReturn
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (sixVertexDegreeTwoAlignedTrueFirstReturnState
          homega heta hdegree x) =
      sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
        homegaSector hetaSector hmiddle
        (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
  let y := doubledAlignedFirstReturnPerm homega heta hdegree x
  let retie := orientedDartAlignedRetie homega heta hdegree y.1
  change sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle
      (if retie.pairingP = retie.pairingQ then y
        else doubledAlignedBranchSwap y) =
    sixVertexDegreeTwoBranchClosedSelected homega heta hdegree middle
      homegaSector hetaSector hmiddle y
  split
  · rfl
  · exact sixVertexDegreeTwoBranchClosedSelected_branchSwap
      homega heta hdegree middle homegaSector hetaSector hmiddle _



noncomputable def sixVertexDegreeTwoAlignedFalseDartSlotSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (dart : FKMedialBlackDart T) : FKMedialBlackDart T :=
  if mask dart.1.1 && (fkMedialVertexParity dart.1.1 == parity) then
    if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm
        (fkMedialBlackDartSwap dart.1.1
          (alignedBlackDartLayerSwap homega heta hdegree dart))
    else fkMedialBlackDartSwap dart.1.1 dart
  else dart

theorem sixVertexDegreeTwoAlignedFalseDartSlotSwap_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (x : DoubledAlignedState omega eta) :
    sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree mask parity
        layer (doubledAlignedBlackDart homega heta hdegree false x) =
      if mask (doubledAlignedVertex x) &&
          (fkMedialVertexParity (doubledAlignedVertex x) == parity) then
        doubledAlignedBlackDart homega heta hdegree false
          (doubledAlignedBranchSwap x)
      else doubledAlignedBlackDart homega heta hdegree false x := by
  have hvertex :
      (doubledAlignedBlackDart homega heta hdegree false x).1.1 =
        doubledAlignedVertex x := by
    simp [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex]
  rw [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hvertex]
  split
  · cases layer
    · exact fkMedialBlackDartSwap_doubledAlignedBlackDart
        homega heta hdegree false x
    · rw [alignedBlackDartLayerSwap_active,
        fkMedialBlackDartSwap_doubledAlignedBlackDart]
      simpa using (congrArg
        (alignedBlackDartLayerSwap homega heta hdegree).symm
        (alignedBlackDartLayerSwap_active homega heta hdegree
          (doubledAlignedBranchSwap x))).symm
  · rfl



theorem sixVertexDegreeTwoBranchClosedFalseDartSlotSwap_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (parity layer : Bool)
    (dart : FKMedialBlackDart T) :
    sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
          (sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta hdegree
            middle homegaSector hetaSector hmiddle layer)
          parity layer dart ∈
        doubledAlignedBoundarySegments homega heta hdegree false
          (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
            homegaSector hetaSector hmiddle) ↔
      dart ∈ doubledAlignedBoundarySegments homega heta hdegree false
        (sixVertexDegreeTwoBranchClosedUnitPrefix homega heta hdegree middle
          homegaSector hetaSector hmiddle) := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta) dart
  · let active : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
    let x := (doubledAlignedBlackDartEquiv
      homega heta hdegree false).symm active
    have hdart : doubledAlignedBlackDart homega heta hdegree false x = dart :=
      congrArg Subtype.val ((doubledAlignedBlackDartEquiv
        homega heta hdegree false).apply_symm_apply active)
    rw [← hdart,
      sixVertexDegreeTwoAlignedFalseDartSlotSwap_active]
    split
    · rw [doubledAlignedBlackDart_mem_boundarySegments_iff,
        doubledAlignedBlackDart_mem_boundarySegments_iff]
      exact sixVertexDegreeTwoBranchClosedUnitPrefix_branchSwap_mem_iff
        homega heta hdegree middle homegaSector hetaSector hmiddle x
    · rfl
  · have hzero := (hdegree dart.1.1).resolve_right hactive
    have hmask := sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
      dart.1.1 hzero
    simp [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hmask]

theorem alignedBlackDartLayerSwap_vertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    (alignedBlackDartLayerSwap homega heta hdegree dart).1.1 = dart.1.1 := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta) dart
  · let active : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
    let x := (doubledAlignedBlackDartEquiv
      homega heta hdegree false).symm active
    have hdart : doubledAlignedBlackDart homega heta hdegree false x =
        dart := congrArg Subtype.val
      ((doubledAlignedBlackDartEquiv
        homega heta hdegree false).apply_symm_apply active)
    rw [← hdart, alignedBlackDartLayerSwap_active]
    simp [doubledAlignedBlackDart, blackDartOfStrandSlot_vertex,
      doubledAlignedVertex]
  · rw [alignedBlackDartLayerSwap_inactive
      homega heta hdegree dart hactive]

theorem alignedBlackDartLayerSwap_symm_vertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    ((alignedBlackDartLayerSwap homega heta hdegree).symm dart).1.1 =
      dart.1.1 := by
  let swap := alignedBlackDartLayerSwap homega heta hdegree
  have h := alignedBlackDartLayerSwap_vertex homega heta hdegree
    (swap.symm dart)
  change (swap (swap.symm dart)).1.1 = (swap.symm dart).1.1 at h
  simpa using h.symm

theorem alignedBlackDartLayerSwap_symm_false_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree x.1
    (alignedBlackDartLayerSwap homega heta hdegree).symm
        (doubledAlignedBlackDart homega heta hdegree false x) =
      doubledAlignedBlackDart homega heta hdegree false
        (if retie.pairingP = retie.pairingQ then x
          else doubledAlignedBranchSwap x) := by
  let retie := orientedDartAlignedRetie homega heta hdegree x.1
  apply (alignedBlackDartLayerSwap homega heta hdegree).injective
  simp only [Equiv.apply_symm_apply]
  by_cases heq : retie.pairingP = retie.pairingQ
  · rw [if_pos heq, alignedBlackDartLayerSwap_active]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree x
    simpa [retie, heq] using hdart.symm
  · rw [if_neg heq, alignedBlackDartLayerSwap_active]
    have hdart := doubledAlignedBlackDart_true_eq_false_or_branchSwap
      homega heta hdegree (doubledAlignedBranchSwap x)
    simpa [retie, heq] using hdart.symm

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T) :
    (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
      homega heta hdegree layer dart).1 = dart.1.1 := by
  cases layer
  · rfl
  · exact (congrArg Prod.fst
      (fkColoredBlackDartStrandSlotEquiv_apply
        (alignedRoutingLoopPairing homega heta hdegree true)
        (alignedBlackDartLayerSwap homega heta hdegree dart))).trans
      (alignedBlackDartLayerSwap_vertex homega heta hdegree dart)

theorem fkColoredParityMaskStrandSlotSwap_slotOfFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (mask : T.Vertex -> Bool) (parity layer : Bool)
    (dart : FKMedialBlackDart T) :
    fkColoredParityMaskStrandSlotSwap mask parity
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (sixVertexDegreeTwoAlignedFalseDartSlotSwap homega heta hdegree
          mask parity layer dart) := by
  by_cases hmask : mask dart.1.1 &&
      (fkMedialVertexParity dart.1.1 == parity)
  · cases layer
    · rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false,
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_false]
      simp only [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hmask, if_true,
        Bool.false_eq_true, if_false]
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      simpa using fkColoredParityMaskStrandSlotSwap_apply_of_true
        mask parity
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree false dart) (by simpa using hmask)
    · let swap := alignedBlackDartLayerSwap homega heta hdegree
      rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true,
        sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
      simp only [sixVertexDegreeTwoAlignedFalseDartSlotSwap, hmask, if_true,
        Equiv.apply_symm_apply]
      rw [fkColoredBlackDartStrandSlot_blackSwap]
      have hselected :
          (mask (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
              homega heta hdegree true dart).1 &&
            (fkMedialVertexParity
              (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
                homega heta hdegree true dart).1 == parity)) = true := by
        rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst]
        exact hmask
      have hswap := fkColoredParityMaskStrandSlotSwap_apply_of_true
        mask parity
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree true dart) hselected
      rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst] at hswap
      simpa only [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_true]
        using hswap
  · have hmaskFalse : (mask dart.1.1 &&
        (fkMedialVertexParity dart.1.1 == parity)) = false :=
      Bool.eq_false_of_not_eq_true hmask
    rw [sixVertexDegreeTwoAlignedFalseDartSlotSwap, if_neg hmask]
    have hunselected :
        (mask (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart).1 &&
          (fkMedialVertexParity
            (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
              homega heta hdegree layer dart).1 == parity)) = false := by
      rw [sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_fst]
      exact hmaskFalse
    exact fkColoredParityMaskStrandSlotSwap_apply_of_false
      mask parity
      (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
        homega heta hdegree layer dart) hunselected


noncomputable def sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) : FKMedialBlackDart T :=
  let mask := sixVertexDegreeTwoBranchClosedExpandedRetieMask
    homega heta hdegree middle homegaSector hetaSector hmiddle layer
  let input := sixVertexDegreeTwoAlignedFalseDartSlotSwap
    homega heta hdegree mask false layer dart
  let arrival := alignedBoundaryPerm homega heta hdegree false input
  let common := if layer then
      (alignedBlackDartLayerSwap homega heta hdegree).symm arrival
    else arrival
  sixVertexDegreeTwoAlignedFalseDartSlotSwap
    homega heta hdegree mask true layer common

theorem sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta
        hdegree middle homegaSector hetaSector hmiddle layer dart =
      alignedBoundaryPerm homega heta hdegree false dart := by
  let mask := sixVertexDegreeTwoBranchClosedExpandedRetieMask homega heta
    hdegree middle homegaSector hetaSector hmiddle layer
  have hzeroD := (hdegree dart.1.1).resolve_right hdart
  have hmaskD : mask dart.1.1 = false :=
    sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive homega heta
      hdegree middle homegaSector hetaSector hmiddle layer dart.1.1 hzeroD
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hzeroNext := (hdegree next.1.1).resolve_right hnext
  have hmaskNext : mask next.1.1 = false :=
    sixVertexDegreeTwoBranchClosedExpandedRetieMask_inactive homega heta
      hdegree middle homegaSector hetaSector hmiddle layer next.1.1 hzeroNext
  have hswapNext : alignedBlackDartLayerSwap homega heta hdegree next = next :=
    alignedBlackDartLayerSwap_inactive homega heta hdegree next hnext
  have hswapNextSymm :
      (alignedBlackDartLayerSwap homega heta hdegree).symm next = next := by
    apply (alignedBlackDartLayerSwap homega heta hdegree).injective
    simpa [hswapNext]
  simp [sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart,
    sixVertexDegreeTwoAlignedFalseDartSlotSwap, mask, next, hmaskD,
    hmaskNext, hswapNextSymm]

theorem sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart
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
        (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta
          hdegree middle homegaSector hetaSector hmiddle layer)
        (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) =
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer
        (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega heta
          hdegree middle homegaSector hetaSector hmiddle layer dart) := by
  rw [sixVertexDegreeTwoBranchClosedExpandedTargetBoundary]
  simp only [Equiv.trans_apply]
  rw [fkColoredParityMaskStrandSlotSwap_slotOfFalseDart,
    sixVertexDegreeTwoAlignedSourceBoundary_slotOfFalseDart,
    fkColoredParityMaskStrandSlotSwap_slotOfFalseDart]
  rfl


noncomputable def sixVertexDegreeTwoAlignedFalseDartOfSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (slot : T.Vertex × Bool) : FKMedialBlackDart T :=
  if layer then
    (alignedBlackDartLayerSwap homega heta hdegree).symm
      ((fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true)).symm slot)
  else
    (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).symm slot

@[simp] theorem sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (slot : T.Vertex × Bool) :
    sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
        layer (sixVertexDegreeTwoAlignedFalseDartOfSlot
          homega heta hdegree layer slot) = slot := by
  cases layer
  · exact (fkColoredBlackDartStrandSlotEquiv
      (alignedRoutingLoopPairing homega heta hdegree false)).apply_symm_apply
        slot
  · simp [sixVertexDegreeTwoAlignedFalseDartOfSlot,
      sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart]



theorem sixVertexDegreeTwoBranchClosedSlotColorInvariant_of_falseDart
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
            (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
              homega heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
              middle homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
              homega heta hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
              homega heta hdegree layer
              (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart
                homega heta hdegree middle homegaSector hetaSector hmiddle
                layer dart))) =
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (fkIndexedOccurrenceSlotEquiv
            (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
              homega heta hdegree middle homegaSector hetaSector hmiddle))
            (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
              middle homegaSector hetaSector hmiddle)
            (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
              homega heta hdegree middle homegaSector hetaSector hmiddle)
            (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
              homega heta hdegree layer dart))) :
    FKColoredIndexedOccurrenceSlotColorInvariant
      (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
      (sixVertexDegreeTwoBranchClosedExpandedTargetPairing homega heta hdegree
        middle homegaSector hetaSector hmiddle)
      (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
        homega heta hdegree middle homegaSector hetaSector hmiddle))
      (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree middle
        homegaSector hetaSector hmiddle)
      (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective homega heta
        hdegree middle homegaSector hetaSector hmiddle) := by
  intro slot
  rcases slot with ⟨layer, slot⟩
  let dart := sixVertexDegreeTwoAlignedFalseDartOfSlot
    homega heta hdegree layer slot
  have hslot := sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart_inverse
    homega heta hdegree layer slot
  change sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree
      layer dart = slot at hslot
  rw [← hslot,
    fkColoredLayeredStrandSlotBoundaryPerm_apply,
    sixVertexDegreeTwoBranchClosedExpandedTargetBoundary_slotOfFalseDart]
  exact hfalseDart layer dart

theorem fkColoredVertexStrandSlotSwap_apply_of_fst_ne
    {T : EvenTorus} (v : T.Vertex) (slot : T.Vertex × Bool)
    (hne : slot.1 ≠ v) :
    fkColoredVertexStrandSlotSwap v slot = slot := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    exact hne (congrArg Prod.fst h)
  · intro h
    exact hne (congrArg Prod.fst h)



theorem fkColoredStrandSlotBoundaryPerm_retie_apply_of_away
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (first second : T.Vertex) (slot : T.Vertex × Bool)
    (hfirst : if fkMedialVertexParity first = true then
        (fkColoredStrandSlotBoundaryPerm pairing slot).1 ≠ first
      else slot.1 ≠ first)
    (hsecond : if fkMedialVertexParity second = true then
        (fkColoredStrandSlotBoundaryPerm pairing slot).1 ≠ second
      else slot.1 ≠ second) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexRetieAtTransitionVertices pairing first second) slot =
      fkColoredStrandSlotBoundaryPerm pairing slot := by
  by_cases hvertices : first = second
  · rw [fkColoredStrandSlotBoundaryPerm_retie_of_eq
      pairing hvertices]
    by_cases hp : fkMedialVertexParity first = true
    · rw [if_pos hp]
      simp only [Equiv.trans_apply]
      exact fkColoredVertexStrandSlotSwap_apply_of_fst_ne first _
        (by simpa [hp] using hfirst)
    · rw [if_neg hp]
      simp only [Equiv.trans_apply]
      rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne first slot
        (by simpa [hp] using hfirst)]
  · have hvertices' : first != second := bne_iff_ne.mpr hvertices
    rw [fkColoredStrandSlotBoundaryPerm_retie_of_ne
      pairing hvertices']
    by_cases hpSecond : fkMedialVertexParity second = true
    · rw [if_pos hpSecond]
      by_cases hpFirst : fkMedialVertexParity first = true
      · rw [if_pos hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne first _
            (by simpa [hpFirst] using hfirst),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne second _
            (by simpa [hpSecond] using hsecond)]
      · rw [if_neg hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne first slot
            (by simpa [hpFirst] using hfirst),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne second _
            (by simpa [hpSecond] using hsecond)]
    · rw [if_neg hpSecond]
      by_cases hpFirst : fkMedialVertexParity first = true
      · rw [if_pos hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne second slot
            (by simpa [hpSecond] using hsecond),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne first _
            (by simpa [hpFirst] using hfirst)]
      · rw [if_neg hpFirst]
        simp only [Equiv.trans_apply]
        rw [fkColoredVertexStrandSlotSwap_apply_of_fst_ne second slot
            (by simpa [hpSecond] using hsecond),
          fkColoredVertexStrandSlotSwap_apply_of_fst_ne first slot
            (by simpa [hpFirst] using hfirst)]



theorem sixVertexDegreeTwoAlignedTargetBoundary_apply_of_away
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle)
    (hleft : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutLeft ≠ [])
    (hright : (canonicalDoubledAlignedOrbitChunkCut homega heta hdegree
      middle homegaSector hetaSector hmiddle).cutRight ≠ [])
    (layer : Bool) (slot : T.Vertex × Bool)
    (hrightAway :
      let rightVertex := doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutRight.head hright)
      if fkMedialVertexParity rightVertex = true then
        (fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer) slot).1 ≠
            rightVertex
      else slot.1 ≠ rightVertex)
    (hleftAway :
      let leftVertex := doubledAlignedVertex
        ((canonicalDoubledAlignedOrbitChunkCut homega heta hdegree middle
          homegaSector hetaSector hmiddle).cutLeft.head hleft)
      if fkMedialVertexParity leftVertex = true then
        (fkColoredStrandSlotBoundaryPerm
          (alignedRoutingLoopPairing homega heta hdegree layer) slot).1 ≠
            leftVertex
      else slot.1 ≠ leftVertex) :
    fkColoredStrandSlotBoundaryPerm
        (sixVertexDegreeTwoAlignedTargetPairing homega heta hdegree middle
          homegaSector hetaSector hmiddle layer) slot =
      fkColoredStrandSlotBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree layer) slot := by
  rw [sixVertexDegreeTwoAlignedTargetPairing_of_proper
    homega heta hdegree middle homegaSector hetaSector hmiddle
    hleft hright layer]
  exact fkColoredStrandSlotBoundaryPerm_retie_apply_of_away _ _ _ _
    hrightAway hleftAway



theorem sixVertexDegreeTwoAlignedTransportedColor_dart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      if _hdart : dart ∈ doubledAlignedBoundarySegments
          homega heta hdegree false
          (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
            homegaSector hetaSector hmiddle) then
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree (!layer) dart)
      else
        fkColoredLayeredSlotColor
          (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart) := by
  classical
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments
      homega heta hdegree false
      (SixVertexDegreeTwoAlignedSelectedStates homega heta hdegree middle
        homegaSector hetaSector hmiddle)
  · rw [dif_pos hdart,
      sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]
  · rw [dif_neg hdart,
      sixVertexDegreeTwoAlignedOccurrenceSlotEquiv_apply_dart_of_not_mem
        homega heta hdegree middle homegaSector hetaSector hmiddle
        layer dart hdart]



theorem sixVertexDegreeTwoAlignedTransportedColor_dart_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) dart)) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) := by
  classical
  rw [sixVertexDegreeTwoAlignedTransportedColor_dart]
  split
  · have hcross :=
      sixVertexDegreeTwoAlignedColoredSource_inactive_dart_color_eq
        homega heta hdegree dart hinactive
    cases layer
    · exact hcross.symm
    · exact hcross
  · rfl



theorem sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer
          (alignedBoundaryPerm homega heta hdegree false dart)) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
          homega heta hdegree layer dart) := by
  let source := sixVertexDegreeTwoAlignedColoredSource homega heta hdegree
  cases layer
  · have hboundary := FKColoredLoopPairing.slotColor_boundaryPerm
      source false
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree false) dart)
    have hpairing : (source false).pairing =
        alignedRoutingLoopPairing homega heta hdegree false := rfl
    rw [hpairing] at hboundary
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply,
      Equiv.symm_apply_apply] at hboundary
    change fkColoredLayeredSlotColor source
        (false, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false)
          (alignedBoundaryPerm homega heta hdegree false dart)) =
      fkColoredLayeredSlotColor source
        (false, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree false) dart)
    exact hboundary
  · let swap := alignedBlackDartLayerSwap homega heta hdegree
    let next := alignedBoundaryPerm homega heta hdegree false dart
    have hnext : alignedBoundaryPerm homega heta hdegree true (swap dart) =
        next := by
      exact (alignedBoundaryPerm_false_eq_true_layerSwap
        homega heta hdegree dart).symm
    have hswapNext : swap next = next :=
      alignedBlackDartLayerSwap_inactive
        homega heta hdegree next hinactive
    have hboundary := FKColoredLoopPairing.slotColor_boundaryPerm
      source true
      (fkColoredBlackDartStrandSlotEquiv
        (alignedRoutingLoopPairing homega heta hdegree true) (swap dart))
    have hpairing : (source true).pairing =
        alignedRoutingLoopPairing homega heta hdegree true := rfl
    rw [hpairing] at hboundary
    simp only [fkColoredStrandSlotBoundaryPerm, Equiv.trans_apply,
      Equiv.symm_apply_apply] at hboundary
    change fkColoredLayeredSlotColor source
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) (swap next)) =
      fkColoredLayeredSlotColor source
        (true, fkColoredBlackDartStrandSlotEquiv
          (alignedRoutingLoopPairing homega heta hdegree true) (swap dart))
    rw [hswapNext]
    have hnext' : fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true) (swap dart) =
        next := hnext
    rw [hnext'] at hboundary
    exact hboundary



theorem sixVertexDegreeTwoBranchClosedExpanded_falseDart_color_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hdart : Not (activeBlackDart (omega := omega) (eta := eta) dart))
    (hnext : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer
            (sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart homega
              heta hdegree middle homegaSector hetaSector hmiddle layer dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoBranchClosedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoBranchClosedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta
            hdegree layer dart)) := by
  rw [sixVertexDegreeTwoBranchClosedExpandedBoundaryFalseDart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart hnext,
    sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer
      (alignedBoundaryPerm homega heta hdegree false dart) hnext,
    sixVertexDegreeTwoBranchClosedTransportedColor_dart_of_inactive
      homega heta hdegree middle homegaSector hetaSector hmiddle layer dart
      hdart]
  exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
    homega heta hdegree layer dart hnext



theorem sixVertexDegreeTwoAlignedTransportedColor_falseBoundary_of_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (middle : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
    (hmiddle : 0 < middle) (layer : Bool)
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart))) :
    fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer
            (alignedBoundaryPerm homega heta hdegree false dart))) =
      fkColoredLayeredSlotColor
        (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree)
        (fkIndexedOccurrenceSlotEquiv
          (Fintype.card (SixVertexDegreeTwoAlignedBoundaryOccurrence
            homega heta hdegree middle homegaSector hetaSector hmiddle))
          (sixVertexDegreeTwoAlignedBoundaryFinKey homega heta hdegree
            middle homegaSector hetaSector hmiddle)
          (sixVertexDegreeTwoAlignedBoundaryFinKey_injective
            homega heta hdegree middle homegaSector hetaSector hmiddle)
          (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart
            homega heta hdegree layer dart)) := by
  classical
  let selected := SixVertexDegreeTwoAlignedSelectedStates
    homega heta hdegree middle homegaSector hetaSector hmiddle
  let next := alignedBoundaryPerm homega heta hdegree false dart
  have hmem : next ∈ doubledAlignedBoundarySegments
        homega heta hdegree false selected ↔
      dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree false selected :=
    mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false selected dart hinactive
  rw [sixVertexDegreeTwoAlignedTransportedColor_dart,
    sixVertexDegreeTwoAlignedTransportedColor_dart]
  by_cases hdart : dart ∈ doubledAlignedBoundarySegments
      homega heta hdegree false selected
  · have hnext : next ∈ doubledAlignedBoundarySegments
        homega heta hdegree false selected := hmem.mpr hdart
    rw [dif_pos hnext, dif_pos hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree (!layer) dart hinactive
  · have hnext : next ∉ doubledAlignedBoundarySegments
        homega heta hdegree false selected := by
      exact fun h => hdart (hmem.mp h)
    rw [dif_neg hnext, dif_neg hdart]
    exact sixVertexDegreeTwoAlignedColoredSource_falseBoundary_color
      homega heta hdegree layer dart hinactive



theorem doubledAlignedBoundarySegments_step_mem_iff_of_state_invariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta))
    (hinvariant : forall y : DoubledAlignedState omega eta,
      y ∈ states ↔
        (doubledAlignedFirstReturnPerm homega heta hdegree).symm y ∈ states)
    (dart : FKMedialBlackDart T) :
    alignedBoundaryPerm homega heta hdegree false dart ∈
        doubledAlignedBoundarySegments homega heta hdegree false states ↔
      dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree false states := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree false dart)
  · let activeArrival : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} :=
      ⟨alignedBoundaryPerm homega heta hdegree false dart, hactive⟩
    let y := (doubledAlignedBlackDartEquiv
      homega heta hdegree false).symm activeArrival
    have hstep : alignedBoundaryPerm homega heta hdegree false dart =
        doubledAlignedBlackDart homega heta hdegree false y := by
      exact congrArg Subtype.val
        ((doubledAlignedBlackDartEquiv
          homega heta hdegree false).apply_symm_apply activeArrival).symm
    rw [hstep,
      doubledAlignedBlackDart_mem_boundarySegments_iff,
      mem_doubledAlignedBoundarySegments_predecessor_iff
        homega heta hdegree states dart y hstep]
    exact hinvariant y
  · exact mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
      homega heta hdegree false states dart hactive

end

end StatMech.FrontierD
