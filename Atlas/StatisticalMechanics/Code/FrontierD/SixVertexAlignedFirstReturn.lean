/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexDegreeTwoDisagreementStrand
import Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample
import Code.FrontierD.FKMedialCheckerboard
import Code.FrontierD.FKMedialBoundaryToggleParity
import Code.FrontierD.FiniteFirstReturn











open StatMech.FrontierD

namespace StatMech.FrontierD

def localMate (pairing : Bool) (d : Fin 4) : Fin 4 :=
  if pairing then ![2, 3, 0, 1] d else ![3, 2, 1, 0] d

def compatible (pairing : Bool)
    (p : SixVertexLocalIncomingPattern) : Prop :=
  if pairing then p 0 != p 2 /\ p 1 != p 3
  else p 0 != p 3 /\ p 1 != p 2

local instance (pairing : Bool) (p : SixVertexLocalIncomingPattern) :
    Decidable (compatible pairing p) := by
  unfold compatible
  infer_instance

def localPreferredPairing (p : SixVertexLocalIncomingPattern) : Bool :=
  if compatible false p then false else true

theorem localPreferredPairing_compatible
    (p : SixVertexLocalIncomingPattern) (hp : p.Ice) :
    compatible (localPreferredPairing p) p := by
  unfold localPreferredPairing compatible at *
  decide +revert

theorem compatible_iff_fkLoopPairingCompatible
    {T : EvenTorus} (omega : SixVertexArrows T)
    (v : T.Vertex) (pairing : Bool) :
    compatible pairing (sixVertexLocalIncomingPattern omega v) <->
      fkLoopPairingCompatible pairing omega v := by
  unfold compatible fkLoopPairingCompatible
    sixVertexLocalIncomingPattern
  cases pairing <;> simp [bne_iff_ne]

def strandSlot (pairing : Bool) (d : Fin 4) : Bool :=
  if pairing then ![false, true, false, true] d
  else ![false, true, true, false] d

def sideVertical (d : Fin 4) : Bool :=
  ![false, false, true, true] d

def horizontalSlot (p : SixVertexLocalIncomingPattern) (side : Bool) : Bool :=
  if side then p 1 else p 0

def localCIndicator (p : SixVertexLocalIncomingPattern) : Nat :=
  if p 0 = p 1 then 1 else 0

noncomputable local instance sixVertexIsCTypeDecidable
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    Decidable (omega.IsCType v) :=
  Classical.propDecidable _

theorem localCIndicator_eq_ite_isCType
    (p : SixVertexLocalIncomingPattern) :
    localCIndicator p = if p.IsCType then 1 else 0 := by
  unfold localCIndicator SixVertexLocalIncomingPattern.IsCType
  decide +revert

theorem localCIndicator_localIncomingPattern
    {T : EvenTorus} (omega : SixVertexArrows T) (v : T.Vertex) :
    localCIndicator (sixVertexLocalIncomingPattern omega v) =
      if omega.IsCType v then 1 else 0 := by
  classical
  rw [localCIndicator_eq_ite_isCType]
  exact if_congr (sixVertexLocalIncomingPattern_isCType_iff omega v) rfl rfl



theorem sixVertexPairTotalC_mono_of_local
    {T : EvenTorus}
    (omega eta omega' eta' : SixVertexArrows T)
    (hlocal : forall v,
      localCIndicator (sixVertexLocalIncomingPattern omega v) +
          localCIndicator (sixVertexLocalIncomingPattern eta v) <=
        localCIndicator (sixVertexLocalIncomingPattern omega' v) +
          localCIndicator (sixVertexLocalIncomingPattern eta' v)) :
    sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount omega' + sixVertexTorusCTypeCount eta' := by
  classical
  simp only [sixVertexTorusCTypeCount, <- Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  simpa only [localCIndicator_localIncomingPattern] using hlocal v




def arrowsOfIncomingPatterns
    {T : EvenTorus} (patterns : T.Vertex -> SixVertexLocalIncomingPattern) :
    SixVertexArrows T where
  horizontal v := !patterns v 1
  vertical v := !patterns v 3

theorem localIncomingPattern_arrowsOfIncomingPatterns
    {T : EvenTorus} (patterns : T.Vertex -> SixVertexLocalIncomingPattern)
    (hwest : forall v,
      patterns v 0 =
        !patterns (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1)
    (hsouth : forall v,
      patterns v 2 =
        !patterns (v.1,
          SixVertexArrows.cyclicPred T.height_pos v.2) 3)
    (v : T.Vertex) :
    sixVertexLocalIncomingPattern (arrowsOfIncomingPatterns patterns) v =
      patterns v := by
  funext d
  fin_cases d
  · simp [sixVertexLocalIncomingPattern, fkLoopWestIncoming,
      arrowsOfIncomingPatterns, hwest]
  · simp [sixVertexLocalIncomingPattern, fkLoopEastIncoming,
      arrowsOfIncomingPatterns]
  · simp [sixVertexLocalIncomingPattern, fkLoopSouthIncoming,
      arrowsOfIncomingPatterns, hsouth]
  · simp [sixVertexLocalIncomingPattern, fkLoopNorthIncoming,
      arrowsOfIncomingPatterns]

theorem arrowsOfIncomingPatterns_ice
    {T : EvenTorus} (patterns : T.Vertex -> SixVertexLocalIncomingPattern)
    (hwest : forall v,
      patterns v 0 =
        !patterns (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1)
    (hsouth : forall v,
      patterns v 2 =
        !patterns (v.1,
          SixVertexArrows.cyclicPred T.height_pos v.2) 3)
    (hice : forall v, (patterns v).Ice) :
    (arrowsOfIncomingPatterns patterns).IceRule := by
  intro v
  rw [<- sixVertexLocalIncomingPattern_count]
  rw [localIncomingPattern_arrowsOfIncomingPatterns
    patterns hwest hsouth v]
  exact hice v

def exchangeLocalSlots (sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun d =>
      if strandSlot false d = sideP then
        horizontalSlot q sideQ
      else p d,
   fun d =>
      if strandSlot false d = sideQ then
        horizontalSlot p sideP
      else q d)

def exchangedLocalCIndicator (sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) : Nat :=
  localCIndicator (exchangeLocalSlots sideP sideQ p q).1 +
    localCIndicator (exchangeLocalSlots sideP sideQ p q).2



def exchangeLocalAlignedMask (select0 select1 sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  (fun d =>
      let branch := strandSlot false d != sideP
      let selected := if branch then select1 else select0
      let sourceQ := if branch then !sideQ else sideQ
      if selected then horizontalSlot q sourceQ else p d,
   fun d =>
      let branch := strandSlot false d != sideQ
      let selected := if branch then select1 else select0
      let sourceP := if branch then !sideP else sideP
      if selected then horizontalSlot p sourceP else q d)

def exchangedLocalAlignedMaskCIndicator
    (select0 select1 sideP sideQ : Bool)
    (p q : SixVertexLocalIncomingPattern) : Nat :=
  localCIndicator
      (exchangeLocalAlignedMask select0 select1 sideP sideQ p q).1 +
    localCIndicator
      (exchangeLocalAlignedMask select0 select1 sideP sideQ p q).2




theorem localCIndicator_exchange_aligned_exit
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalCIndicator
        (strandSlot pairingP d)
        (strandSlot pairingQ
          (localMate pairingQ (localMate pairingP d))) p q =
      localCIndicator p + localCIndicator q := by
  unfold compatible exchangedLocalCIndicator exchangeLocalSlots
    localCIndicator horizontalSlot strandSlot localMate at *
  decide +revert




theorem exists_compatible_aligned_exit_pairings
    (p q : SixVertexLocalIncomingPattern)
    (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) :
    exists pairingP pairingQ : Bool,
      compatible pairingP p /\ compatible pairingQ q /\
        p (localMate pairingQ (localMate pairingP d)) !=
          q (localMate pairingQ (localMate pairingP d)) := by
  unfold compatible localMate at *
  decide +revert

structure AlignedExitRetie
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4) where
  pairingP : Bool
  pairingQ : Bool
  compatibleP : compatible pairingP p
  compatibleQ : compatible pairingQ q
  partnerDisagrees :
    p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))

noncomputable def canonicalAlignedExitRetie
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) : AlignedExitRetie p q d := by
  let hex := exists_compatible_aligned_exit_pairings
    p q d hp hq hdegree hd
  let pairingP := Classical.choose hex
  let hexQ := Classical.choose_spec hex
  let pairingQ := Classical.choose hexQ
  let hspec := Classical.choose_spec hexQ
  exact ⟨pairingP, pairingQ, hspec.1, hspec.2.1, hspec.2.2⟩

def AlignedExitRetie.slotP
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Bool :=
  strandSlot retie.pairingP d

def AlignedExitRetie.partnerSide
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Fin 4 :=
  localMate retie.pairingQ (localMate retie.pairingP d)

def AlignedExitRetie.slotQ
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Bool :=
  strandSlot retie.pairingQ retie.partnerSide

theorem localMate_involutive (pairing : Bool) (d : Fin 4) :
    localMate pairing (localMate pairing d) = d := by
  cases pairing <;> fin_cases d <;> rfl



theorem AlignedExitRetie.common_exit
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) :
    localMate retie.pairingP d =
      localMate retie.pairingQ retie.partnerSide := by
  unfold AlignedExitRetie.partnerSide
  rw [localMate_involutive]

def boundaryAlignedSlotQRaw (vertexParity pairingP pairingQ : Bool)
    (d : Fin 4) : Bool :=
  let exit := localMate pairingP d
  let partner := localMate pairingQ exit
  let slotQ := strandSlot pairingQ partner
  let flip := (pairingP != pairingQ) &&
    (vertexParity == sideVertical exit)
  if flip then !slotQ else slotQ

def boundaryAlignedSlotQ (vertexParity : Bool)
    {p q : SixVertexLocalIncomingPattern} {d : Fin 4}
    (retie : AlignedExitRetie p q d) : Bool :=
  boundaryAlignedSlotQRaw vertexParity retie.pairingP retie.pairingQ d



def blackSideIndexOfStrandSlot
    (vertexParity pairing slot : Bool) : Bool :=
  slot ^^ (vertexParity && !pairing)

noncomputable def blackDartOfStrandSlot
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) : FKMedialBlackDart T :=
  (fkMedialBlackDartEquivVertexBool T).symm
    (slot.1, blackSideIndexOfStrandSlot
      (fkMedialVertexParity slot.1) (pairing slot.1) slot.2)

@[simp] theorem blackDartOfStrandSlot_vertex
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (slot : T.Vertex × Bool) :
    (blackDartOfStrandSlot pairing slot).1.1 = slot.1 := by
  have h := congrArg Prod.fst
    ((fkMedialBlackDartEquivVertexBool T).apply_symm_apply
      (slot.1, blackSideIndexOfStrandSlot
        (fkMedialVertexParity slot.1) (pairing slot.1) slot.2))
  exact h

def strandSlotOfBlackDart
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) : Bool :=
  fkMedialBlackSideIndex d.1.2 ^^
    (fkMedialVertexParity d.1.1 && !pairing d.1.1)

theorem blackDartOfStrandSlot_injective
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    Function.Injective (blackDartOfStrandSlot pairing) := by
  rintro ⟨v, side⟩ ⟨w, side'⟩ h
  have hfixed := congrArg (fkMedialBlackDartEquivVertexBool T) h
  simp only [blackDartOfStrandSlot, Equiv.apply_symm_apply] at hfixed
  change (v, blackSideIndexOfStrandSlot
      (fkMedialVertexParity v) (pairing v) side) =
    (w, blackSideIndexOfStrandSlot
      (fkMedialVertexParity w) (pairing w) side') at hfixed
  have hv : v = w := congrArg Prod.fst hfixed
  subst w
  apply Prod.ext
  · rfl
  · have hs := congrArg Prod.snd hfixed
    cases hp : pairing v <;> cases hvp : fkMedialVertexParity v <;>
      cases side <;> cases side' <;>
      simp [blackSideIndexOfStrandSlot, hp, hvp] at hs ⊢

@[simp] theorem blackDartOfStrandSlot_strandSlotOfBlackDart
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T) :
    blackDartOfStrandSlot pairing (d.1.1,
      strandSlotOfBlackDart pairing d) = d := by
  apply (fkMedialBlackDartEquivVertexBool T).injective
  simp only [blackDartOfStrandSlot, Equiv.apply_symm_apply]
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases side <;> cases hp : pairing v <;>
    cases hv : fkMedialVertexParity v <;>
    simp [strandSlotOfBlackDart,
      blackSideIndexOfStrandSlot, fkMedialBlackDartEquivVertexBool,
      fkMedialBlackDart0, fkMedialBlackDart1,
      fkMedialCheckerColor, fkMedialSideVertical, hp, hv] at hd ⊢




theorem blackBoundary_alignedSlot_first_step
    {T : EvenTorus} (pairingP pairingQ : FKMedialLoopPairing T)
    (v : T.Vertex) (localP localQ branch : Bool) (d : Fin 4)
    (hP : pairingP v = localP) (hQ : pairingQ v = localQ) :
    fkMedialBlackBoundaryPerm pairingP
        (blackDartOfStrandSlot pairingP
          (v, if branch then !strandSlot localP d else strandSlot localP d)) =
      fkMedialBlackBoundaryPerm pairingQ
        (blackDartOfStrandSlot pairingQ
          (v, if branch then
            !boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              localP localQ d
          else boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              localP localQ d)) := by
  apply Subtype.ext
  rw [fkMedialBlackBoundaryPerm_val, fkMedialBlackBoundaryPerm_val]
  cases localP <;> cases localQ <;> cases branch <;>
    cases hv : fkMedialVertexParity v <;> fin_cases d <;>
    simp [blackDartOfStrandSlot, blackSideIndexOfStrandSlot,
      fkMedialBlackDartEquivVertexBool, fkMedialBlackDart0,
      fkMedialBlackDart1, boundaryAlignedSlotQRaw, strandSlot,
      sideVertical, localMate, fkMedialLocalMate, hP, hQ, hv]

theorem blackBoundary_eq_of_pairing_eq_at
    {T : EvenTorus} (pairingP pairingQ : FKMedialLoopPairing T)
    (d : FKMedialBlackDart T)
    (hlocal : pairingP d.1.1 = pairingQ d.1.1) :
    fkMedialBlackBoundaryPerm pairingP d =
      fkMedialBlackBoundaryPerm pairingQ d := by
  apply Subtype.ext
  rw [fkMedialBlackBoundaryPerm_val, fkMedialBlackBoundaryPerm_val]
  rcases d with ⟨⟨v, side⟩, hd⟩
  cases side <;> simp [fkMedialLocalMate, hlocal]




theorem exists_boundaryAligned_localC_defect :
    exists p q : SixVertexLocalIncomingPattern,
      p.Ice /\ q.Ice /\
      (sixVertexLocalDisagreementSides p q).card = 2 /\
      compatible false p /\ compatible true q /\
      p (2 : Fin 4) != q (2 : Fin 4) /\
      p (localMate true (localMate false (2 : Fin 4))) !=
        q (localMate true (localMate false (2 : Fin 4))) /\
      exchangedLocalCIndicator (strandSlot false (2 : Fin 4))
          (boundaryAlignedSlotQRaw false false true (2 : Fin 4)) p q !=
        localCIndicator p + localCIndicator q := by
  decide



theorem localCIndicator_exchange_boundary_aligned_exact
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalCIndicator (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q =
      localCIndicator p + localCIndicator q +
        if (pairingP != pairingQ) &&
            (vertexParity != sideVertical d) then 2 else 0 := by
  unfold boundaryAlignedSlotQRaw
    compatible exchangedLocalCIndicator exchangeLocalSlots
    localCIndicator horizontalSlot strandSlot sideVertical localMate at *
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;> fin_cases d
  all_goals decide +revert

set_option maxHeartbeats 1000000 in




theorem localCIndicator_exchange_boundary_aligned_mask_exact
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity select0 select1 : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    exchangedLocalAlignedMaskCIndicator select0 select1
        (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q =
      localCIndicator p + localCIndicator q +
        if (select0 != select1) && (pairingP != pairingQ) &&
            (vertexParity != sideVertical d) then 2 else 0 := by
  unfold boundaryAlignedSlotQRaw compatible
    exchangedLocalAlignedMaskCIndicator exchangeLocalAlignedMask
    localCIndicator horizontalSlot strandSlot sideVertical localMate at *
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;>
    cases select0 <;> cases select1 <;> fin_cases d
  all_goals decide +revert

set_option maxHeartbeats 1000000 in




theorem boundaryAlignedSlotColor_bne
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    ((vertexParity ^^ horizontalSlot p (strandSlot pairingP d)) !=
      (vertexParity ^^ horizontalSlot q
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d))) =
      ((pairingP == pairingQ) ||
        (vertexParity != sideVertical d)) := by
  unfold SixVertexLocalIncomingPattern.Ice compatible
    sixVertexLocalDisagreementSides localMate strandSlot horizontalSlot
    boundaryAlignedSlotQRaw sideVertical at *
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;> fin_cases d
  all_goals decide +revert

set_option maxHeartbeats 1000000 in


theorem boundaryAlignedComplementSlotColor_bne
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    ((vertexParity ^^ horizontalSlot p (!strandSlot pairingP d)) !=
      (vertexParity ^^ horizontalSlot q
        (!boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d))) =
      ((pairingP != pairingQ) &&
        (vertexParity != sideVertical d)) := by
  unfold SixVertexLocalIncomingPattern.Ice compatible
    sixVertexLocalDisagreementSides localMate strandSlot horizontalSlot
    boundaryAlignedSlotQRaw sideVertical at *
  cases pairingP <;> cases pairingQ <;> cases vertexParity <;> fin_cases d
  all_goals decide +revert

set_option maxHeartbeats 1000000 in



theorem boundaryAlignedSlotQRaw_complement_color_bne_of_pairing_ne
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d)))
    (hne : pairingP != pairingQ) :
    ((vertexParity ^^ horizontalSlot q
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d)) !=
      (vertexParity ^^ horizontalSlot q
        (!boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d))) =
      true := by
  unfold SixVertexLocalIncomingPattern.Ice compatible
    sixVertexLocalDisagreementSides localMate horizontalSlot
    boundaryAlignedSlotQRaw sideVertical at *
  cases pairingP <;> cases pairingQ <;> simp at hne
  all_goals cases vertexParity <;> fin_cases d
  all_goals decide +revert

theorem localCIndicator_le_exchange_boundary_aligned_mask
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity select0 select1 : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    localCIndicator p + localCIndicator q <=
      exchangedLocalAlignedMaskCIndicator select0 select1
        (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q := by
  rw [localCIndicator_exchange_boundary_aligned_mask_exact p q pairingP
    pairingQ vertexParity select0 select1 d hp hq hdegree hcompatibleP
    hcompatibleQ hd hpartner]
  exact Nat.le_add_right _ _

theorem localCIndicator_le_exchange_boundary_aligned
    (p q : SixVertexLocalIncomingPattern)
    (pairingP pairingQ vertexParity : Bool) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hcompatibleP : compatible pairingP p)
    (hcompatibleQ : compatible pairingQ q)
    (hd : p d != q d)
    (hpartner : p (localMate pairingQ (localMate pairingP d)) !=
      q (localMate pairingQ (localMate pairingP d))) :
    localCIndicator p + localCIndicator q <=
      exchangedLocalCIndicator (strandSlot pairingP d)
        (boundaryAlignedSlotQRaw vertexParity pairingP pairingQ d) p q := by
  rw [localCIndicator_exchange_boundary_aligned_exact p q pairingP pairingQ
    vertexParity d hp hq hdegree hcompatibleP hcompatibleQ hd hpartner]
  exact Nat.le_add_right _ _

theorem canonicalAlignedExitRetie_nondecreases_localC
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (vertexParity : Bool)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) :
    let retie := canonicalAlignedExitRetie p q d hp hq hdegree hd
    localCIndicator p + localCIndicator q <=
      exchangedLocalCIndicator retie.slotP
        (boundaryAlignedSlotQ vertexParity retie) p q := by
  dsimp only [AlignedExitRetie.slotP, boundaryAlignedSlotQ]
  apply localCIndicator_le_exchange_boundary_aligned p q
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingQ
    vertexParity d hp hq hdegree
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleQ hd
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).partnerDisagrees

theorem canonicalAlignedExitRetie_preserves_localC
    (p q : SixVertexLocalIncomingPattern) (d : Fin 4)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2)
    (hd : p d != q d) :
    let retie := canonicalAlignedExitRetie p q d hp hq hdegree hd
    exchangedLocalCIndicator retie.slotP retie.slotQ p q =
      localCIndicator p + localCIndicator q := by
  dsimp only [AlignedExitRetie.slotP, AlignedExitRetie.slotQ,
    AlignedExitRetie.partnerSide]
  apply localCIndicator_exchange_aligned_exit p q
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).pairingQ d
    hp hq hdegree
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleP
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).compatibleQ hd
    (canonicalAlignedExitRetie p q d hp hq hdegree hd).partnerDisagrees

noncomputable def orientedDartAlignedRetie
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    AlignedExitRetie
      (sixVertexLocalIncomingPattern omega d.1.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1.1) d.1.1.2 :=
  canonicalAlignedExitRetie
    (sixVertexLocalIncomingPattern omega d.1.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1.1) d.1.1.2
    (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
    (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
    (sixVertexDisagreementDart_local_card_eq_two hdegree d.1)
    (by
      have hd := sixVertexDisagreementDart_side_mem d.1
      rw [mem_sixVertexLocalDisagreementSides] at hd
      exact bne_iff_ne.mpr hd)

noncomputable def orientedDartAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) : Bool :=
  let retie := orientedDartAlignedRetie homega heta hdegree d
  if layer then retie.slotQ else retie.slotP




noncomputable def orientedDartBoundaryAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) : Bool :=
  let retie := orientedDartAlignedRetie homega heta hdegree d
  if layer then
    boundaryAlignedSlotQ (fkMedialVertexParity d.1.1.1) retie
  else retie.slotP

def orientedBlockVertices
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (block : List (SixVertexOrientedDisagreementDart omega eta)) :
    List T.Vertex :=
  block.map fun d => d.1.1.1

noncomputable def orientedBlockSlotOf
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (block : List (SixVertexOrientedDisagreementDart omega eta))
    (layer : Bool) (i : Fin (orientedBlockVertices block).length) : Bool :=
  let j : Fin block.length := ⟨i.val, by simpa [orientedBlockVertices] using i.isLt⟩
  orientedDartAlignedSlot homega heta hdegree layer (block.get j)

theorem orientedDartAlignedRetie_preserves_localC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    let retie := orientedDartAlignedRetie homega heta hdegree d
    exchangedLocalCIndicator retie.slotP retie.slotQ
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) =
      localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) := by
  apply canonicalAlignedExitRetie_preserves_localC

theorem orientedDartBoundaryAlignedRetie_nondecreases_localC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalCIndicator
        (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
        (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) := by
  change let retie := orientedDartAlignedRetie homega heta hdegree d
    localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalCIndicator retie.slotP
        (boundaryAlignedSlotQ (fkMedialVertexParity d.1.1.1) retie)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1)
  apply canonicalAlignedExitRetie_nondecreases_localC

theorem orientedDartBoundaryAlignedMask_nondecreases_localC
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : Bool)
    (d : SixVertexOrientedDisagreementDart omega eta) :
    localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalAlignedMaskCIndicator select0 select1
        (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
        (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) := by
  let retie := orientedDartAlignedRetie homega heta hdegree d
  change localCIndicator
          (sixVertexLocalIncomingPattern omega d.1.1.1) +
        localCIndicator
          (sixVertexLocalIncomingPattern eta d.1.1.1) <=
      exchangedLocalAlignedMaskCIndicator select0 select1
        (strandSlot retie.pairingP d.1.1.2)
        (boundaryAlignedSlotQRaw (fkMedialVertexParity d.1.1.1)
          retie.pairingP retie.pairingQ d.1.1.2)
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1)
  apply localCIndicator_le_exchange_boundary_aligned_mask
    (sixVertexLocalIncomingPattern omega d.1.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1.1)
    retie.pairingP retie.pairingQ
    (fkMedialVertexParity d.1.1.1) select0 select1 d.1.1.2
  · exact sixVertexLocalIncomingPattern_ice omega homega d.1.1.1
  · exact sixVertexLocalIncomingPattern_ice eta heta d.1.1.1
  · exact sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  · exact retie.compatibleP
  · exact retie.compatibleQ
  · have hd := sixVertexDisagreementDart_side_mem d.1
    rw [mem_sixVertexLocalDisagreementSides] at hd
    exact bne_iff_ne.mpr hd
  · exact retie.partnerDisagrees

theorem orientedDisagreementDart_eq_of_vertex_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d e : SixVertexOrientedDisagreementDart omega eta)
    (hvertex : d.1.1.1 = e.1.1.1) : d = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact hvertex
  · by_contra hside
    have hcard := sixVertexDisagreementDart_local_card_eq_two hdegree d.1
    have hdmem := sixVertexDisagreementDart_side_mem d.1
    have hemem : e.1.1.2 ∈ sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega d.1.1.1)
        (sixVertexLocalIncomingPattern eta d.1.1.1) := by
      rw [hvertex]
      exact sixVertexDisagreementDart_side_mem e.1
    have hne := sixVertexLocalIncoming_ne_at_two_disagreements
      (sixVertexLocalIncomingPattern omega d.1.1.1)
      (sixVertexLocalIncomingPattern eta d.1.1.1)
      d.1.1.2 e.1.1.2
      (sixVertexLocalIncomingPattern_ice omega homega d.1.1.1)
      (sixVertexLocalIncomingPattern_ice eta heta d.1.1.1)
      hcard hdmem hemem (Ne.symm hside)
    apply hne
    rw [d.2]
    have he := e.2
    change sixVertexLocalIncomingPattern omega e.1.1.1 e.1.1.2 = true
      at he
    rwa [hvertex]

theorem exists_incoming_disagreement_side
    (p q : SixVertexLocalIncomingPattern)
    (hp : p.Ice) (hq : q.Ice)
    (hdegree : (sixVertexLocalDisagreementSides p q).card = 2) :
    exists d : Fin 4, p d != q d /\ p d = true := by
  decide +revert

noncomputable def orientedDisagreementDartAtActiveVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    SixVertexOrientedDisagreementDart omega eta := by
  let hex := exists_incoming_disagreement_side
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern eta v)
    (sixVertexLocalIncomingPattern_ice omega homega v)
    (sixVertexLocalIncomingPattern_ice eta heta v) hactive
  let side := Classical.choose hex
  let hs := Classical.choose_spec hex
  let dart : SixVertexDisagreementDart omega eta :=
    ⟨(v, side), by
      change sixVertexTorusEdgeDisagrees omega eta
        (sixVertexTorusIncidentEdge T v side)
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      exact bne_iff_ne.mp hs.1⟩
  exact ⟨dart, hs.2⟩

abbrev DoubledAlignedState
    {T : EvenTorus} (omega eta : SixVertexArrows T) :=
  SixVertexOrientedDisagreementDart omega eta × Bool



def doubledAlignedBranchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) : DoubledAlignedState omega eta :=
  (x.1, !x.2)

@[simp] theorem doubledAlignedBranchSwap_fst
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) :
    (doubledAlignedBranchSwap x).1 = x.1 := rfl

@[simp] theorem doubledAlignedBranchSwap_self
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBranchSwap (doubledAlignedBranchSwap x) = x := by
  rcases x with ⟨d, branch⟩
  cases branch <;>
    simp [doubledAlignedBranchSwap]

noncomputable def alignedMaskedLocalPair
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool) (v : T.Vertex) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hv
    exchangeLocalAlignedMask (select0 v) (select1 v)
      (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
      (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)
  else
    (sixVertexLocalIncomingPattern omega v,
      sixVertexLocalIncomingPattern eta v)

noncomputable def alignedStateSelectorBranchMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (selected : DoubledAlignedState omega eta -> Bool)
    (branch : Bool) (v : T.Vertex) : Bool :=
  if hv : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    selected (orientedDisagreementDartAtActiveVertex
      homega heta v hv, branch)
  else false

def alignedStateListSelector
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (states : List (DoubledAlignedState omega eta))
    (x : DoubledAlignedState omega eta) : Bool :=
  decide (x ∈ states)

noncomputable def alignedStateListBranchMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (states : List (DoubledAlignedState omega eta))
    (branch : Bool) (v : T.Vertex) : Bool :=
  alignedStateSelectorBranchMask homega heta
    (alignedStateListSelector states) branch v

noncomputable def alignedMaskedLocalPattern
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (layer : Bool) (v : T.Vertex) : SixVertexLocalIncomingPattern :=
  if layer then
    (alignedMaskedLocalPair homega heta hdegree select0 select1 v).2
  else (alignedMaskedLocalPair homega heta hdegree select0 select1 v).1

noncomputable def alignedMaskedTarget
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (layer : Bool) : SixVertexArrows T :=
  arrowsOfIncomingPatterns
    (alignedMaskedLocalPattern homega heta hdegree select0 select1 layer)

def AlignedMaskedBondConsistent
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool) : Prop :=
  (forall (layer : Bool) (v : T.Vertex),
    alignedMaskedLocalPattern homega heta hdegree
        select0 select1 layer v 0 =
      !alignedMaskedLocalPattern homega heta hdegree select0 select1 layer
        (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1) /\
  (forall (layer : Bool) (v : T.Vertex),
    alignedMaskedLocalPattern homega heta hdegree
        select0 select1 layer v 2 =
      !alignedMaskedLocalPattern homega heta hdegree select0 select1 layer
        (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) 3)

theorem alignedMaskedTarget_localIncomingPattern
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hbond : AlignedMaskedBondConsistent
      homega heta hdegree select0 select1)
    (layer : Bool) (v : T.Vertex) :
    sixVertexLocalIncomingPattern
        (alignedMaskedTarget homega heta hdegree select0 select1 layer) v =
      alignedMaskedLocalPattern homega heta hdegree
        select0 select1 layer v := by
  apply localIncomingPattern_arrowsOfIncomingPatterns
  · exact hbond.1 layer
  · exact hbond.2 layer




theorem sixVertexPairTotalC_mono_of_alignedLocalMask
    {T : EvenTorus} {omega eta omega' eta' : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hactive : forall (v : T.Vertex)
      (hv : (sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 2),
      let d := orientedDisagreementDartAtActiveVertex
        homega heta v hv
      (sixVertexLocalIncomingPattern omega' v,
          sixVertexLocalIncomingPattern eta' v) =
        exchangeLocalAlignedMask (select0 v) (select1 v)
          (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
          (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
          (sixVertexLocalIncomingPattern omega v)
          (sixVertexLocalIncomingPattern eta v))
    (hinactive : forall (v : T.Vertex)
      (_hv : (sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 0),
      (sixVertexLocalIncomingPattern omega' v,
          sixVertexLocalIncomingPattern eta' v) =
        (sixVertexLocalIncomingPattern omega v,
          sixVertexLocalIncomingPattern eta v)) :
    sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount omega' + sixVertexTorusCTypeCount eta' := by
  apply sixVertexPairTotalC_mono_of_local
  intro v
  rcases hdegree v with hzero | htwo
  · have h := hinactive v hzero
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    dsimp only at hfirst hsecond
    rw [hfirst, hsecond]
  · let d := orientedDisagreementDartAtActiveVertex
      homega heta v htwo
    have h := hactive v htwo
    change (sixVertexLocalIncomingPattern omega' v,
        sixVertexLocalIncomingPattern eta' v) =
      exchangeLocalAlignedMask (select0 v) (select1 v)
        (orientedDartBoundaryAlignedSlot homega heta hdegree false d)
        (orientedDartBoundaryAlignedSlot homega heta hdegree true d)
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v) at h
    have hfirst := congrArg Prod.fst h
    have hsecond := congrArg Prod.snd h
    dsimp only at hfirst hsecond
    rw [hfirst, hsecond]
    exact orientedDartBoundaryAlignedMask_nondecreases_localC
      homega heta hdegree (select0 v) (select1 v) d

theorem alignedMaskedTarget_totalC_mono
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (select0 select1 : T.Vertex -> Bool)
    (hbond : AlignedMaskedBondConsistent
      homega heta hdegree select0 select1) :
    sixVertexTorusCTypeCount omega + sixVertexTorusCTypeCount eta <=
      sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree select0 select1 false) +
        sixVertexTorusCTypeCount
          (alignedMaskedTarget homega heta hdegree select0 select1 true) := by
  apply sixVertexPairTotalC_mono_of_alignedLocalMask
    homega heta hdegree select0 select1
  · intro v hv
    rw [alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond false v,
      alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond true v]
    simp [alignedMaskedLocalPattern, alignedMaskedLocalPair, hv]
  · intro v hv
    have hnot : Not ((sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 2) := by omega
    rw [alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond false v,
      alignedMaskedTarget_localIncomingPattern
        homega heta hdegree select0 select1 hbond true v]
    simp [alignedMaskedLocalPattern, alignedMaskedLocalPair, hnot]

theorem localIncomingPattern_eq_of_disagreement_card_zero
    (p q : SixVertexLocalIncomingPattern)
    (hzero : (sixVertexLocalDisagreementSides p q).card = 0) :
    p = q := by
  funext d
  by_contra hne
  have hmem : d ∈ sixVertexLocalDisagreementSides p q :=
    (mem_sixVertexLocalDisagreementSides p q d).2 hne
  have hpos : 0 < (sixVertexLocalDisagreementSides p q).card :=
    Finset.card_pos.mpr ⟨d, hmem⟩
  omega




noncomputable def alignedRoutingPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) : Bool :=
  if hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 then
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    let retie := orientedDartAlignedRetie homega heta hdegree d
    if layer then retie.pairingQ else retie.pairingP
  else if layer then
    localPreferredPairing (sixVertexLocalIncomingPattern eta v)
  else localPreferredPairing (sixVertexLocalIncomingPattern omega v)

theorem alignedRoutingPairing_compatible
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) :
    fkLoopPairingCompatible
      (alignedRoutingPairing homega heta hdegree layer v)
      (if layer then eta else omega) v := by
  unfold alignedRoutingPairing
  split
  · rename_i hactive
    let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
    have hdv : d.1.1.1 = v := rfl
    cases layer
    · apply (compatible_iff_fkLoopPairingCompatible omega v _).1
      exact (orientedDartAlignedRetie homega heta hdegree d).compatibleP
    · apply (compatible_iff_fkLoopPairingCompatible eta v _).1
      exact (orientedDartAlignedRetie homega heta hdegree d).compatibleQ
  · cases layer
    · apply (compatible_iff_fkLoopPairingCompatible omega v _).1
      exact localPreferredPairing_compatible _
        (sixVertexLocalIncomingPattern_ice omega homega v)
    · apply (compatible_iff_fkLoopPairingCompatible eta v _).1
      exact localPreferredPairing_compatible _
        (sixVertexLocalIncomingPattern_ice eta heta v)

noncomputable def alignedRoutingLoopPairing
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) : FKMedialLoopPairing T :=
  alignedRoutingPairing homega heta hdegree layer

theorem alignedRoutingPairing_eq_at_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex)
    (hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) :
    alignedRoutingPairing homega heta hdegree layer v =
      let d := orientedDisagreementDartAtActiveVertex homega heta v hactive
      let retie := orientedDartAlignedRetie homega heta hdegree d
      if layer then retie.pairingQ else retie.pairingP := by
  simp only [alignedRoutingPairing, dif_pos hactive]

theorem alignedRoutingPairing_eq_layers_at_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (v : T.Vertex)
    (hzero : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 0) :
    alignedRoutingPairing homega heta hdegree false v =
      alignedRoutingPairing homega heta hdegree true v := by
  have hnot : Not ((sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2) := by omega
  rw [alignedRoutingPairing, dif_neg hnot,
    alignedRoutingPairing, dif_neg hnot]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [localIncomingPattern_eq_of_disagreement_card_zero _ _ hzero]

noncomputable def doubledAlignedSlot
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) : Bool :=
  let selected := orientedDartBoundaryAlignedSlot
    homega heta hdegree layer x.1
  if x.2 then !selected else selected

@[simp] theorem doubledAlignedSlot_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    doubledAlignedSlot homega heta hdegree layer
        (doubledAlignedBranchSwap x) =
      !doubledAlignedSlot homega heta hdegree layer x := by
  rcases x with ⟨d, branch⟩
  cases branch <;>
    simp [doubledAlignedBranchSwap, doubledAlignedSlot]

def doubledAlignedVertex
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) : T.Vertex :=
  x.1.1.1.1

@[simp] theorem doubledAlignedVertex_branchSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (x : DoubledAlignedState omega eta) :
    doubledAlignedVertex (doubledAlignedBranchSwap x) =
      doubledAlignedVertex x := rfl



theorem doubledAlignedState_eq_or_branchSwap_of_vertex_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x y : DoubledAlignedState omega eta)
    (hvertex : doubledAlignedVertex x = doubledAlignedVertex y) :
    y = x ∨ y = doubledAlignedBranchSwap x := by
  have hdart : y.1 = x.1 :=
    orientedDisagreementDart_eq_of_vertex_eq
      homega heta hdegree y.1 x.1 hvertex.symm
  rcases x with ⟨d, firstBranch⟩
  rcases y with ⟨e, secondBranch⟩
  simp only at hdart
  subst e
  cases firstBranch <;> cases secondBranch <;>
    simp [doubledAlignedBranchSwap]

noncomputable def doubledAlignedBlackDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (x : DoubledAlignedState omega eta) :
    FKMedialBlackDart T :=
  blackDartOfStrandSlot
    (alignedRoutingLoopPairing homega heta hdegree layer)
    (doubledAlignedVertex x,
      doubledAlignedSlot homega heta hdegree layer x)



theorem doubledAlignedBlackDart_first_step
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree false)
        (doubledAlignedBlackDart homega heta hdegree false x) =
      fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true)
        (doubledAlignedBlackDart homega heta hdegree true x) := by
  rcases x with ⟨d, branch⟩
  let v := d.1.1.1
  have hactive : (sixVertexLocalDisagreementSides
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)).card = 2 :=
    sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  let d0 := orientedDisagreementDartAtActiveVertex
    homega heta v hactive
  have hd0 : d0 = d := orientedDisagreementDart_eq_of_vertex_eq
    homega heta hdegree d0 d rfl
  have hP := alignedRoutingPairing_eq_at_active
    homega heta hdegree false v hactive
  have hQ := alignedRoutingPairing_eq_at_active
    homega heta hdegree true v hactive
  change alignedRoutingPairing homega heta hdegree false v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingP at hP
  change alignedRoutingPairing homega heta hdegree true v =
      (orientedDartAlignedRetie homega heta hdegree d0).pairingQ at hQ
  rw [hd0] at hP hQ
  change fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree false)
        (blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree false)
          (v, if branch then
            !strandSlot
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
                d.1.1.2
          else strandSlot
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
                d.1.1.2)) =
      fkMedialBlackBoundaryPerm
        (alignedRoutingLoopPairing homega heta hdegree true)
        (blackDartOfStrandSlot
          (alignedRoutingLoopPairing homega heta hdegree true)
          (v, if branch then
            !boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
              (orientedDartAlignedRetie homega heta hdegree d).pairingQ
                d.1.1.2
          else boundaryAlignedSlotQRaw (fkMedialVertexParity v)
              (orientedDartAlignedRetie homega heta hdegree d).pairingP
              (orientedDartAlignedRetie homega heta hdegree d).pairingQ
                d.1.1.2))
  exact blackBoundary_alignedSlot_first_step
    (alignedRoutingLoopPairing homega heta hdegree false)
    (alignedRoutingLoopPairing homega heta hdegree true) v
    (orientedDartAlignedRetie homega heta hdegree d).pairingP
    (orientedDartAlignedRetie homega heta hdegree d).pairingQ branch
    d.1.1.2 hP hQ

noncomputable def doubledAlignedSlotEmbedding
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    DoubledAlignedState omega eta ↪ T.Vertex × Bool where
  toFun x := (doubledAlignedVertex x,
    doubledAlignedSlot homega heta hdegree layer x)
  inj' := by
    intro x y hxy
    change (doubledAlignedVertex x,
      doubledAlignedSlot homega heta hdegree layer x) =
      (doubledAlignedVertex y,
        doubledAlignedSlot homega heta hdegree layer y) at hxy
    have hv : doubledAlignedVertex x = doubledAlignedVertex y :=
      congrArg (fun z : T.Vertex × Bool => z.1) hxy
    have hd : x.1 = y.1 := orientedDisagreementDart_eq_of_vertex_eq
      homega heta hdegree x.1 y.1 hv
    rcases x with ⟨d, branchX⟩
    rcases y with ⟨e, branchY⟩
    simp only at hd
    subst e
    apply Prod.ext
    · rfl
    · have hs := congrArg (fun z : T.Vertex × Bool => z.2) hxy
      change (if branchX then
          !orientedDartBoundaryAlignedSlot homega heta hdegree layer d
        else orientedDartBoundaryAlignedSlot homega heta hdegree layer d) =
        (if branchY then
          !orientedDartBoundaryAlignedSlot homega heta hdegree layer d
        else orientedDartBoundaryAlignedSlot homega heta hdegree layer d) at hs
      cases branchX <;> cases branchY <;> simp_all

theorem mem_range_doubledAlignedSlotEmbedding_iff_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (v : T.Vertex) (side : Bool) :
    (v, side) ∈ Set.range
        (doubledAlignedSlotEmbedding homega heta hdegree layer) ↔
      (sixVertexLocalDisagreementSides
        (sixVertexLocalIncomingPattern omega v)
        (sixVertexLocalIncomingPattern eta v)).card = 2 := by
  constructor
  · rintro ⟨⟨d, branch⟩, h⟩
    have hv : d.1.1.1 = v := by
      exact congrArg (fun z : T.Vertex × Bool => z.1) h
    rw [← hv]
    exact sixVertexDisagreementDart_local_card_eq_two hdegree d.1
  · intro hactive
    let d := orientedDisagreementDartAtActiveVertex
      homega heta v hactive
    let selected := orientedDartBoundaryAlignedSlot
      homega heta hdegree layer d
    by_cases hs : side = selected
    · refine ⟨(d, false), ?_⟩
      change (doubledAlignedVertex (d, false),
        doubledAlignedSlot homega heta hdegree layer (d, false)) =
        (v, side)
      apply Prod.ext
      · rfl
      · change selected = side
        exact hs.symm
    · have hs' : side = !selected := by
        cases side <;> cases hsel : selected <;> simp_all
      refine ⟨(d, true), ?_⟩
      change (doubledAlignedVertex (d, true),
        doubledAlignedSlot homega heta hdegree layer (d, true)) =
        (v, side)
      apply Prod.ext
      · rfl
      · change Bool.not selected = side
        exact hs'.symm

def activeBlackDart
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (d : FKMedialBlackDart T) : Prop :=
  (sixVertexLocalDisagreementSides
    (sixVertexLocalIncomingPattern omega d.1.1)
    (sixVertexLocalIncomingPattern eta d.1.1)).card = 2

noncomputable local instance activeBlackDartDecidable
    {T : EvenTorus} {omega eta : SixVertexArrows T} :
    DecidablePred (activeBlackDart (omega := omega) (eta := eta)) :=
  Classical.decPred _

theorem doubledAlignedBlackDart_injective
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    Function.Injective
      (doubledAlignedBlackDart homega heta hdegree layer) := by
  intro x y hxy
  apply (doubledAlignedSlotEmbedding
    homega heta hdegree layer).injective
  apply blackDartOfStrandSlot_injective
  exact hxy

theorem doubledAlignedBlackDart_surjective_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    Function.Surjective (fun x : DoubledAlignedState omega eta =>
      (⟨doubledAlignedBlackDart homega heta hdegree layer x,
        by simpa [activeBlackDart, doubledAlignedBlackDart,
            doubledAlignedVertex] using
          sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1⟩ :
        {d : FKMedialBlackDart T //
          activeBlackDart (omega := omega) (eta := eta) d})) := by
  classical
  rintro ⟨d, hd⟩
  let pairing := alignedRoutingLoopPairing homega heta hdegree layer
  let side := strandSlotOfBlackDart pairing d
  have hrange : (d.1.1, side) ∈ Set.range
      (doubledAlignedSlotEmbedding homega heta hdegree layer) :=
    (mem_range_doubledAlignedSlotEmbedding_iff_active
      homega heta hdegree layer d.1.1 side).2 hd
  obtain ⟨x, hx⟩ := hrange
  refine ⟨x, ?_⟩
  apply Subtype.ext
  change (doubledAlignedVertex x,
    doubledAlignedSlot homega heta hdegree layer x) =
      (d.1.1, side) at hx
  change blackDartOfStrandSlot pairing
      (doubledAlignedVertex x,
        doubledAlignedSlot homega heta hdegree layer x) = d
  rw [hx]
  exact blackDartOfStrandSlot_strandSlotOfBlackDart pairing d

noncomputable def doubledAlignedBlackDartEquiv
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) :
    DoubledAlignedState omega eta ≃
      {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} :=
  Equiv.ofBijective
    (fun x =>
      (⟨doubledAlignedBlackDart homega heta hdegree layer x,
        by simpa [activeBlackDart, doubledAlignedBlackDart,
            doubledAlignedVertex] using
          sixVertexDisagreementDart_local_card_eq_two hdegree x.1.1⟩ :
        {d : FKMedialBlackDart T //
          activeBlackDart (omega := omega) (eta := eta) d}))
    ⟨fun x y h => doubledAlignedBlackDart_injective
        homega heta hdegree layer (congrArg Subtype.val h),
      doubledAlignedBlackDart_surjective_active
        homega heta hdegree layer⟩

noncomputable def alignedBoundaryPerm
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) : Equiv.Perm (FKMedialBlackDart T) :=
  fkMedialBlackBoundaryPerm
    (alignedRoutingLoopPairing homega heta hdegree layer)

theorem alignedFirstReturnTime_eq
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    finiteFirstReturnTime
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree false x) =
      finiteFirstReturnTime
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree true x) := by
  classical
  apply finiteFirstReturnTime_eq_of_aligned_first
    (alignedBoundaryPerm homega heta hdegree false)
    (alignedBoundaryPerm homega heta hdegree true)
    (activeBlackDart (omega := omega) (eta := eta))
    (activeBlackDart (omega := omega) (eta := eta)) (fun a b => a = b)
  · intro a b hab
    subst b
    rfl
  · intro a b hab hnotA hnotB
    subst b
    apply blackBoundary_eq_of_pairing_eq_at
    apply alignedRoutingPairing_eq_layers_at_inactive
      homega heta hdegree a.1.1
    rcases hdegree a.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hnotA htwo)
  · exact doubledAlignedBlackDart_first_step
      homega heta hdegree x

theorem alignedFirstReturn_common_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree false x)).1 =
      (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree true x)).1 := by
  classical
  apply finiteFirstReturn_related_of_aligned_first
    (alignedBoundaryPerm homega heta hdegree false)
    (alignedBoundaryPerm homega heta hdegree true)
    (activeBlackDart (omega := omega) (eta := eta))
    (activeBlackDart (omega := omega) (eta := eta)) (fun a b => a = b)
  · intro a b hab
    subst b
    rfl
  · intro a b hab hnotA hnotB
    subst b
    apply blackBoundary_eq_of_pairing_eq_at
    apply alignedRoutingPairing_eq_layers_at_inactive
      homega heta hdegree a.1.1
    rcases hdegree a.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hnotA htwo)
  · exact doubledAlignedBlackDart_first_step
      homega heta hdegree x



noncomputable def doubledAlignedBoundarySegments
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta)) :
    List (FKMedialBlackDart T) :=
  finiteFirstReturnSegments
    (alignedBoundaryPerm homega heta hdegree layer)
    (activeBlackDart (omega := omega) (eta := eta))
    (states.map (doubledAlignedBlackDartEquiv
      homega heta hdegree layer))

theorem doubledAlignedBoundarySegments_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (hstates : states.Nodup) :
    (doubledAlignedBoundarySegments
      homega heta hdegree layer states).Nodup := by
  classical
  apply finiteFirstReturnSegments_nodup
  exact hstates.map
    (doubledAlignedBlackDartEquiv homega heta hdegree layer).injective

theorem mem_doubledAlignedBoundarySegments_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (d : FKMedialBlackDart T) :
    d ∈ doubledAlignedBoundarySegments homega heta hdegree layer states ↔
      ∃ x ∈ states, ∃ k : Nat,
        k < finiteFirstReturnTime
          (alignedBoundaryPerm homega heta hdegree layer)
          (activeBlackDart (omega := omega) (eta := eta))
          (doubledAlignedBlackDartEquiv homega heta hdegree layer x) ∧
        (alignedBoundaryPerm homega heta hdegree layer ^ k)
          (doubledAlignedBlackDart homega heta hdegree layer x) = d := by
  classical
  simp only [doubledAlignedBoundarySegments, finiteFirstReturnSegments,
    List.mem_flatMap, List.mem_map, finiteFirstReturnSegment,
    List.mem_ofFn]
  constructor
  · rintro ⟨active, ⟨x, hx, rfl⟩, ⟨k, hk⟩⟩
    exact ⟨x, hx, k.val, k.isLt, hk⟩
  · rintro ⟨x, hx, k, hk, hd⟩
    exact ⟨doubledAlignedBlackDartEquiv
      homega heta hdegree layer x, ⟨x, hx, rfl⟩,
      ⟨⟨k, hk⟩, hd⟩⟩

theorem mem_doubledAlignedBoundarySegments_step_iff_of_inactive_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (dart : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
      (alignedBoundaryPerm homega heta hdegree layer dart))) :
    alignedBoundaryPerm homega heta hdegree layer dart ∈
        doubledAlignedBoundarySegments homega heta hdegree layer states ↔
      dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree layer states := by
  exact mem_finiteFirstReturnSegments_step_iff_of_not_selected
    (alignedBoundaryPerm homega heta hdegree layer)
    (activeBlackDart (omega := omega) (eta := eta))
    (states.map (doubledAlignedBlackDartEquiv
      homega heta hdegree layer)) dart hinactive

theorem doubledAlignedBlackDart_mem_boundarySegments_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (layer : Bool) (states : List (DoubledAlignedState omega eta))
    (y : DoubledAlignedState omega eta) :
    doubledAlignedBlackDart homega heta hdegree layer y ∈
        doubledAlignedBoundarySegments
          homega heta hdegree layer states ↔
      y ∈ states := by
  classical
  rw [mem_doubledAlignedBoundarySegments_iff]
  constructor
  · rintro ⟨x, hx, k, hk, hpow⟩
    by_cases hkzero : k = 0
    · subst k
      have hxy : x = y :=
        doubledAlignedBlackDart_injective homega heta hdegree layer
          (by simpa using hpow)
      simpa [hxy] using hx
    · have hactive : activeBlackDart (omega := omega) (eta := eta)
          ((alignedBoundaryPerm homega heta hdegree layer ^ k)
            (doubledAlignedBlackDart homega heta hdegree layer x)) := by
        rw [hpow]
        exact (doubledAlignedBlackDartEquiv
          homega heta hdegree layer y).2
      exact False.elim ((finiteFirstReturnTime_minimal
        (alignedBoundaryPerm homega heta hdegree layer)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree layer x) k hk)
          ⟨Nat.pos_of_ne_zero hkzero, hactive⟩)
  · intro hy
    refine ⟨y, hy, 0, finiteFirstReturnTime_pos
      (alignedBoundaryPerm homega heta hdegree layer)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv
        homega heta hdegree layer y), ?_⟩
    simp

theorem length_doubledAlignedBoundarySegments_eq_layers
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta)) :
    (doubledAlignedBoundarySegments homega heta hdegree false states).length =
      (doubledAlignedBoundarySegments
        homega heta hdegree true states).length := by
  classical
  induction states with
  | nil => simp [doubledAlignedBoundarySegments,
      finiteFirstReturnSegments]
  | cons x states ih =>
      simp only [doubledAlignedBoundarySegments,
        finiteFirstReturnSegments, List.map_cons, List.flatMap_cons,
        List.length_append, length_finiteFirstReturnSegment]
      rw [alignedFirstReturnTime_eq homega heta hdegree x]
      exact congrArg
        (fun n => finiteFirstReturnTime
            (alignedBoundaryPerm homega heta hdegree true)
            (activeBlackDart (omega := omega) (eta := eta))
            (doubledAlignedBlackDartEquiv
              homega heta hdegree true x) + n) ih



noncomputable def alignedActiveBlackDartLayerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} :=
  (doubledAlignedBlackDartEquiv homega heta hdegree false).symm.trans
    (doubledAlignedBlackDartEquiv homega heta hdegree true)

noncomputable def alignedBlackDartLayerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (FKMedialBlackDart T) :=
  (alignedActiveBlackDartLayerSwap homega heta hdegree).extendDomain
    (Equiv.refl {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d})

theorem alignedBlackDartLayerSwap_active
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    alignedBlackDartLayerSwap homega heta hdegree
        (doubledAlignedBlackDart homega heta hdegree false x) =
      doubledAlignedBlackDart homega heta hdegree true x := by
  let activeFalse := doubledAlignedBlackDartEquiv
    homega heta hdegree false x
  have himage : (activeFalse : FKMedialBlackDart T) =
      (Equiv.refl {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}) activeFalse := rfl
  change ((alignedActiveBlackDartLayerSwap homega heta hdegree).extendDomain
      (Equiv.refl {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d}))
      (activeFalse : FKMedialBlackDart T) = _
  rw [himage, Equiv.Perm.extendDomain_apply_image]
  change (alignedActiveBlackDartLayerSwap homega heta hdegree
      activeFalse).1 = _
  unfold alignedActiveBlackDartLayerSwap
  simp [activeFalse]
  rfl

theorem alignedBlackDartLayerSwap_inactive
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (d : FKMedialBlackDart T)
    (hinactive : Not (activeBlackDart (omega := omega) (eta := eta) d)) :
    alignedBlackDartLayerSwap homega heta hdegree d = d := by
  exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hinactive





theorem alignedBoundaryPerm_false_eq_true_layerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (dart : FKMedialBlackDart T) :
    alignedBoundaryPerm homega heta hdegree false dart =
      alignedBoundaryPerm homega heta hdegree true
        (alignedBlackDartLayerSwap homega heta hdegree dart) := by
  classical
  by_cases hactive : activeBlackDart (omega := omega) (eta := eta) dart
  · let active : {d : FKMedialBlackDart T //
        activeBlackDart (omega := omega) (eta := eta) d} := ⟨dart, hactive⟩
    let x := (doubledAlignedBlackDartEquiv homega heta hdegree false).symm
      active
    have hdart : doubledAlignedBlackDart homega heta hdegree false x =
        dart := by
      exact congrArg Subtype.val
        ((doubledAlignedBlackDartEquiv homega heta hdegree false).apply_symm_apply
          active)
    rw [← hdart, alignedBlackDartLayerSwap_active]
    exact doubledAlignedBlackDart_first_step homega heta hdegree x
  · rw [alignedBlackDartLayerSwap_inactive
      homega heta hdegree dart hactive]
    apply blackBoundary_eq_of_pairing_eq_at
    apply alignedRoutingPairing_eq_layers_at_inactive
      homega heta hdegree dart.1.1
    rcases hdegree dart.1.1 with hzero | htwo
    · exact hzero
    · exact False.elim (hactive htwo)

theorem alignedBlackDartLayerSwap_power
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) (k : Nat)
    (hk : k < finiteFirstReturnTime
      (alignedBoundaryPerm homega heta hdegree false)
      (activeBlackDart (omega := omega) (eta := eta))
      (doubledAlignedBlackDartEquiv homega heta hdegree false x)) :
    alignedBlackDartLayerSwap homega heta hdegree
        ((alignedBoundaryPerm homega heta hdegree false ^ k)
          (doubledAlignedBlackDart homega heta hdegree false x)) =
      (alignedBoundaryPerm homega heta hdegree true ^ k)
        (doubledAlignedBlackDart homega heta hdegree true x) := by
  classical
  by_cases hkzero : k = 0
  · subst k
    simpa using alignedBlackDartLayerSwap_active
      homega heta hdegree x
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
    have htime := alignedFirstReturnTime_eq homega heta hdegree x
    have hrelated := finiteRelated_until_firstReturn
      (alignedBoundaryPerm homega heta hdegree false)
      (alignedBoundaryPerm homega heta hdegree true)
      (activeBlackDart (omega := omega) (eta := eta))
      (activeBlackDart (omega := omega) (eta := eta))
      (fun a b => a = b)
      (fun {a b} hab hnotA hnotB => by
        subst b
        apply blackBoundary_eq_of_pairing_eq_at
        apply alignedRoutingPairing_eq_layers_at_inactive
          homega heta hdegree a.1.1
        rcases hdegree a.1.1 with hzero | htwo
        · exact hzero
        · exact False.elim (hnotA htwo))
      (doubledAlignedBlackDartEquiv homega heta hdegree false x)
      (doubledAlignedBlackDartEquiv homega heta hdegree true x)
      (doubledAlignedBlackDart_first_step homega heta hdegree x)
      k hkpos (Nat.le_of_lt hk) (by omega)
    have hinactive : Not (activeBlackDart (omega := omega) (eta := eta)
        ((alignedBoundaryPerm homega heta hdegree false ^ k)
          (doubledAlignedBlackDart homega heta hdegree false x))) := by
      intro hactive
      exact (finiteFirstReturnTime_minimal
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree false x)
        k hk) ⟨hkpos, hactive⟩
    rw [alignedBlackDartLayerSwap_inactive
      homega heta hdegree _ hinactive]
    exact hrelated

theorem finiteFirstReturnSegment_aligned_eq_map_layerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    finiteFirstReturnSegment
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree true x) =
      (finiteFirstReturnSegment
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv homega heta hdegree false x)).map
          (alignedBlackDartLayerSwap homega heta hdegree) := by
  classical
  apply List.ext_getElem
  · simp only [length_finiteFirstReturnSegment, List.length_map]
    exact (alignedFirstReturnTime_eq homega heta hdegree x).symm
  · intro k hkTrue hkMap
    simp only [finiteFirstReturnSegment, List.getElem_ofFn,
      List.getElem_map]
    exact (alignedBlackDartLayerSwap_power
      homega heta hdegree x k (by simpa using hkMap)).symm

theorem doubledAlignedBoundarySegments_eq_map_layerSwap
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta)) :
    doubledAlignedBoundarySegments homega heta hdegree true states =
      (doubledAlignedBoundarySegments
        homega heta hdegree false states).map
          (alignedBlackDartLayerSwap homega heta hdegree) := by
  classical
  induction states with
  | nil => simp [doubledAlignedBoundarySegments,
      finiteFirstReturnSegments]
  | cons x states ih =>
      simp only [doubledAlignedBoundarySegments,
        finiteFirstReturnSegments, List.map_cons, List.flatMap_cons,
        List.map_append]
      rw [finiteFirstReturnSegment_aligned_eq_map_layerSwap
        homega heta hdegree x]
      exact congrArg
        (List.append
          ((finiteFirstReturnSegment
            (alignedBoundaryPerm homega heta hdegree false)
            (activeBlackDart (omega := omega) (eta := eta))
            (doubledAlignedBlackDartEquiv
              homega heta hdegree false x)).map
                (alignedBlackDartLayerSwap homega heta hdegree))) ih




noncomputable def doubledAlignedFirstReturnPerm
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    Equiv.Perm (DoubledAlignedState omega eta) :=
  (doubledAlignedBlackDartEquiv homega heta hdegree false).trans
    ((finiteFirstReturnPerm
      (alignedBoundaryPerm homega heta hdegree false)
      (activeBlackDart (omega := omega) (eta := eta))).trans
      (doubledAlignedBlackDartEquiv
        homega heta hdegree false).symm)

@[simp] theorem doubledAlignedFirstReturnPerm_false_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedBlackDartEquiv homega heta hdegree false
        (doubledAlignedFirstReturnPerm homega heta hdegree x) =
      finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree false x) := by
  classical
  simp [doubledAlignedFirstReturnPerm]

theorem doubledAlignedFirstReturnPerm_true_common_arrival
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    (finiteFirstReturn
        (alignedBoundaryPerm homega heta hdegree true)
        (activeBlackDart (omega := omega) (eta := eta))
        (doubledAlignedBlackDartEquiv
          homega heta hdegree true x)).1 =
      (doubledAlignedBlackDartEquiv homega heta hdegree false
        (doubledAlignedFirstReturnPerm homega heta hdegree x)).1 := by
  classical
  rw [doubledAlignedFirstReturnPerm_false_arrival]
  exact (alignedFirstReturn_common_arrival
    homega heta hdegree x).symm




theorem mem_doubledAlignedBoundarySegments_predecessor_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (states : List (DoubledAlignedState omega eta))
    (dart : FKMedialBlackDart T) (y : DoubledAlignedState omega eta)
    (hstep : alignedBoundaryPerm homega heta hdegree false dart =
      doubledAlignedBlackDart homega heta hdegree false y) :
    dart ∈ doubledAlignedBoundarySegments
        homega heta hdegree false states ↔
      (doubledAlignedFirstReturnPerm
        homega heta hdegree).symm y ∈ states := by
  let activeY : {d : FKMedialBlackDart T //
      activeBlackDart (omega := omega) (eta := eta) d} :=
    doubledAlignedBlackDartEquiv homega heta hdegree false y
  have hgeneric := mem_finiteFirstReturnSegments_predecessor_iff
    (alignedBoundaryPerm homega heta hdegree false)
    (activeBlackDart (omega := omega) (eta := eta))
    (states.map (doubledAlignedBlackDartEquiv
      homega heta hdegree false)) dart activeY hstep
  rw [show doubledAlignedBoundarySegments homega heta hdegree false states =
      finiteFirstReturnSegments
        (alignedBoundaryPerm homega heta hdegree false)
        (activeBlackDart (omega := omega) (eta := eta))
        (states.map (doubledAlignedBlackDartEquiv
          homega heta hdegree false)) by rfl]
  rw [hgeneric]
  simp only [List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    have hstate : x = (doubledAlignedFirstReturnPerm
        homega heta hdegree).symm y := by
      apply (doubledAlignedBlackDartEquiv
        homega heta hdegree false).injective
      rw [heq]
      simp [activeY, doubledAlignedFirstReturnPerm]
    simpa [hstate] using hx
  · intro hx
    refine ⟨(doubledAlignedFirstReturnPerm
      homega heta hdegree).symm y, hx, ?_⟩
    simp [activeY, doubledAlignedFirstReturnPerm]



theorem exists_aligned_chunk_split_of_flatten_eq_append
    {A : Type*} (chunks : List (List A))
    (hchunks : chunks ≠ [])
    (hnonempty : forall chunk, chunk ∈ chunks -> chunk ≠ [])
    (left right : List A) (hsplit : chunks.flatten = left ++ right) :
    exists before chunk after chunkLeft chunkRight,
      chunks = before ++ chunk :: after /\
        chunk = chunkLeft ++ chunkRight /\
        left = before.flatten ++ chunkLeft /\
        right = chunkRight ++ after.flatten := by
  induction chunks generalizing left right with
  | nil => exact False.elim (hchunks rfl)
  | cons chunk chunks ih =>
      have hchunk : chunk ≠ [] := hnonempty chunk (by simp)
      have htailNonempty : forall c, c ∈ chunks -> c ≠ [] := by
        intro c hc
        exact hnonempty c (by simp [hc])
      simp only [List.flatten_cons] at hsplit
      rcases List.append_eq_append_iff.mp hsplit with hlong | hshort
      · obtain ⟨tailLeft, hleft, htail⟩ := hlong
        by_cases hnil : chunks = []
        · subst chunks
          have hlen := congrArg List.length htail
          simp only [List.flatten_nil, List.length_nil,
            List.length_append] at hlen
          have htailLeftNil : tailLeft = [] :=
            List.length_eq_zero_iff.mp (by omega)
          have hrightNil : right = [] :=
            List.length_eq_zero_iff.mp (by omega)
          subst tailLeft
          subst right
          exact ⟨[], chunk, [], chunk, [], by simp, by simp,
            by simpa using hleft, by simp⟩
        · obtain ⟨before, cut, after, cutLeft, cutRight,
              hchunks', hcut, htailLeft, hright⟩ :=
            ih hnil htailNonempty tailLeft right htail
          exact ⟨chunk :: before, cut, after, cutLeft, cutRight,
            by simp [hchunks'], hcut, by simp [hleft, htailLeft], hright⟩
      · obtain ⟨chunkRight, hchunkSplit, hright⟩ := hshort
        exact ⟨[], chunk, chunks, left, chunkRight,
          by simp, hchunkSplit, by simp, hright⟩

noncomputable def alignedPermOrderedCycleFactorLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List (List D) :=
  sigma.cycleFactorsFinset.toList.map fun cycle =>
    if hcycle : cycle ∈ sigma.cycleFactorsFinset then
      permOrderedCycleFactor sigma cycle hcycle
    else []

theorem flatten_alignedPermOrderedCycleFactorLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedCycleFactorLists sigma).flatten =
      permOrderedAllCycles sigma := by
  unfold alignedPermOrderedCycleFactorLists permOrderedAllCycles List.flatMap
  rfl

theorem alignedPermOrderedCycleFactorLists_chunk_ne_nil
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedCycleFactorLists sigma) :
    chunk ≠ [] := by
  classical
  rw [alignedPermOrderedCycleFactorLists] at hchunk
  obtain ⟨cycle, hcycleList, rfl⟩ := List.mem_map.mp hchunk
  have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
    simpa using hcycleList
  rw [dif_pos hcycle]
  intro hnil
  have hlen : (permOrderedCycleFactor sigma cycle hcycle).length =
      orderOf cycle := by simp [permOrderedCycleFactor]
  rw [hnil] at hlen
  simp only [List.length_nil] at hlen
  exact (orderOf_pos cycle).ne' hlen.symm

theorem permOrderedCycleFactor_getElem_succ
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset)
    (k : Nat)
    (hk : k + 1 < (permOrderedCycleFactor sigma cycle hcycle).length) :
    sigma (permOrderedCycleFactor sigma cycle hcycle)[k] =
      (permOrderedCycleFactor sigma cycle hcycle)[k + 1] := by
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  let enumerate := permCycleFinEquivSupport cycle hc seed
  simp only [permOrderedCycleFactor, List.getElem_ofFn]
  have hkOrder : k < orderOf cycle := by
    simpa [permOrderedCycleFactor] using
      Nat.lt_trans (by omega : k < k + 1) hk
  let i : Fin (orderOf cycle) := ⟨k, hkOrder⟩
  have hi : (enumerate i).1 ∈ cycle.support := (enumerate i).2
  rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2
    (enumerate i).1 hi]
  change cycle ((cycle ^ k) seed.1) = (cycle ^ (k + 1)) seed.1
  rw [show k + 1 = Nat.succ k by omega, pow_succ']
  rfl

theorem permOrderedCycleFactor_getElem_last
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset)
    (hnonempty : permOrderedCycleFactor sigma cycle hcycle ≠ []) :
    sigma ((permOrderedCycleFactor sigma cycle hcycle).getLast hnonempty) =
      (permOrderedCycleFactor sigma cycle hcycle).head hnonempty := by
  have horder : 0 < orderOf cycle := orderOf_pos cycle
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  simp only [permOrderedCycleFactor, List.getElem_ofFn, List.length_ofFn]
  change sigma ((cycle ^ (orderOf cycle - 1)) seed.1) =
    (cycle ^ 0) seed.1
  have hi : (cycle ^ (orderOf cycle - 1)) seed.1 ∈ cycle.support :=
    Equiv.Perm.pow_apply_mem_support.mpr seed.2
  rw [← (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).2
    ((cycle ^ (orderOf cycle - 1)) seed.1) hi]
  calc
    cycle ((cycle ^ (orderOf cycle - 1)) seed.1) =
        (cycle ^ Nat.succ (orderOf cycle - 1)) seed.1 := by
      rw [pow_succ']
      rfl
    _ = (cycle ^ orderOf cycle) seed.1 := by
      rw [show Nat.succ (orderOf cycle - 1) = orderOf cycle by omega]
    _ = (cycle ^ 0) seed.1 := by rw [pow_orderOf_eq_one]; rfl



noncomputable def alignedPermOrderedFixedPoints
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List D :=
  (Finset.univ.filter fun d => sigma d = d).toList

noncomputable def alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List D :=
  permOrderedAllCycles sigma ++ alignedPermOrderedFixedPoints sigma

noncomputable def alignedPermOrderedAllOrbitLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) : List (List D) :=
  alignedPermOrderedCycleFactorLists sigma ++
    (alignedPermOrderedFixedPoints sigma).map fun d => [d]

theorem flatten_alignedPermOrderedAllOrbitLists
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedAllOrbitLists sigma).flatten =
      alignedPermOrderedAllOrbits sigma := by
  rw [alignedPermOrderedAllOrbitLists, List.flatten_append,
    flatten_alignedPermOrderedCycleFactorLists]
  have hsingle (items : List D) :
      (items.map fun d => [d]).flatten = items := by
    induction items with
    | nil => rfl
    | cons d items ih => simp [ih]
  rw [hsingle]
  rfl

theorem alignedPermOrderedAllOrbitLists_chunk_ne_nil
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
    chunk ≠ [] := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · exact alignedPermOrderedCycleFactorLists_chunk_ne_nil
      sigma chunk hfactor
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfixed
    simp

theorem alignedPermOrderedAllOrbitLists_getElem_succ
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (k : Nat) (hk : k + 1 < chunk.length) :
    sigma chunk[k] = chunk[k + 1] := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · rw [alignedPermOrderedCycleFactorLists] at hfactor
    obtain ⟨cycle, hcycleList, rfl⟩ := List.mem_map.mp hfactor
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    simp only [dif_pos hcycle] at hk ⊢
    exact permOrderedCycleFactor_getElem_succ sigma cycle hcycle k hk
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfixed
    simp at hk

theorem alignedPermOrderedAllOrbitLists_getLast
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hnonempty : chunk ≠ []) :
    sigma (chunk.getLast hnonempty) = chunk.head hnonempty := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · rw [alignedPermOrderedCycleFactorLists] at hfactor
    obtain ⟨cycle, hcycleList, rfl⟩ := List.mem_map.mp hfactor
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    simp only [dif_pos hcycle] at hnonempty ⊢
    exact permOrderedCycleFactor_getElem_last sigma cycle hcycle
      hnonempty
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hfixed
    change sigma d = d
    simpa [alignedPermOrderedFixedPoints] using hd

theorem alignedPermOrderedAllOrbitLists_mem_forward
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (x : D) (hx : x ∈ chunk) :
    sigma x ∈ chunk := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  by_cases hsucc : k + 1 < chunk.length
  · rw [← hget,
      alignedPermOrderedAllOrbitLists_getElem_succ
        sigma chunk hchunk k hsucc]
    exact List.getElem_mem hsucc
  · have hne : chunk ≠ [] :=
      alignedPermOrderedAllOrbitLists_chunk_ne_nil sigma chunk hchunk
    have hkLast : k = chunk.length - 1 := by omega
    have hxLast : chunk.getLast hne = x := by
      rw [List.getLast_eq_getElem]
      subst k
      exact hget
    rw [← hxLast,
      alignedPermOrderedAllOrbitLists_getLast sigma chunk hchunk hne]
    exact List.head_mem hne

theorem alignedPermOrderedAllOrbitLists_mem_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (x : D) :
    sigma x ∈ chunk ↔ x ∈ chunk := by
  constructor
  · intro hsx
    have hpow : forall k : Nat, (sigma ^ k) (sigma x) ∈ chunk := by
      intro k
      induction k with
      | zero => simpa using hsx
      | succ k ih =>
          rw [pow_succ']
          exact alignedPermOrderedAllOrbitLists_mem_forward
            sigma chunk hchunk _ ih
    have hlast := hpow (orderOf sigma - 1)
    have heq : (sigma ^ (orderOf sigma - 1)) (sigma x) = x := by
      calc
        (sigma ^ (orderOf sigma - 1)) (sigma x) =
            (sigma ^ ((orderOf sigma - 1) + 1)) x := by
          rw [pow_succ]
          rfl
        _ = (sigma ^ orderOf sigma) x := by
          rw [show orderOf sigma - 1 + 1 = orderOf sigma by
            have := orderOf_pos sigma
            omega]
        _ = x := by rw [pow_orderOf_eq_one]; rfl
    rwa [heq] at hlast
  · exact alignedPermOrderedAllOrbitLists_mem_forward
      sigma chunk hchunk x

theorem alignedPermOrderedOrbitChunk_left_forward_of_ne_last
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ [])
    (x : D) (hx : x ∈ left)
    (hne : x ≠ left.getLast hleft) :
    sigma x ∈ left := by
  subst chunk
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  have hkNext : k + 1 < left.length := by
    by_contra hnot
    have hkLast : k = left.length - 1 := by omega
    apply hne
    rw [List.getLast_eq_getElem]
    subst k
    exact hget.symm
  have hsucc := alignedPermOrderedAllOrbitLists_getElem_succ
    sigma (left ++ right) hchunk k (by simp; omega)
  rw [List.getElem_append_left hk,
    List.getElem_append_left hkNext] at hsucc
  rw [← hget, hsucc]
  exact List.getElem_mem hkNext

theorem alignedPermOrderedOrbitChunk_right_forward_of_ne_last
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hright : right ≠ [])
    (x : D) (hx : x ∈ right)
    (hne : x ≠ right.getLast hright) :
    sigma x ∈ right := by
  subst chunk
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hx
  have hkNext : k + 1 < right.length := by
    by_contra hnot
    have hkLast : k = right.length - 1 := by omega
    apply hne
    rw [List.getLast_eq_getElem]
    subst k
    exact hget.symm
  have hsucc := alignedPermOrderedAllOrbitLists_getElem_succ
    sigma (left ++ right) hchunk (left.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega),
    List.getElem_append_right (by omega)] at hsucc
  have hsucc' : sigma right[k] = right[k + 1] := by
    calc
      sigma right[k] =
          sigma right[left.length + k - left.length] := by
        congr 1
        exact getElem_congr rfl (by omega) _
      _ = right[left.length + k + 1 - left.length] := hsucc
      _ = right[k + 1] := getElem_congr rfl (by omega) _
  rw [← hget, hsucc']
  exact List.getElem_mem hkNext

theorem alignedPermOrderedOrbitChunk_split_boundary
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ []) :
    sigma (left.getLast hleft) = right.head hright := by
  subst chunk
  have hleftPos : 0 < left.length := List.length_pos_of_ne_nil hleft
  have hrightPos : 0 < right.length := List.length_pos_of_ne_nil hright
  have hsucc := alignedPermOrderedAllOrbitLists_getElem_succ
    sigma (left ++ right) hchunk (left.length - 1) (by simp; omega)
  rw [List.getLast_eq_getElem, List.head_eq_getElem]
  rw [List.getElem_append_left (by omega)] at hsucc
  rw [List.getElem_append_right (by omega)] at hsucc
  calc
    sigma left[left.length - 1] =
        right[left.length - 1 + 1 - left.length] := hsucc
    _ = right[0] := getElem_congr rfl (by omega) _

theorem alignedPermOrderedOrbitChunk_split_entry_boundary
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ []) :
    sigma (right.getLast hright) = left.head hleft := by
  have hne : chunk ≠ [] := by
    rw [hsplit]
    exact List.append_ne_nil_of_left_ne_nil hleft right
  have hcycle := alignedPermOrderedAllOrbitLists_getLast
    sigma chunk hchunk hne
  have hlast : chunk.getLast hne = right.getLast hright := by
    have happ : left ++ right ≠ [] :=
      List.append_ne_nil_of_right_ne_nil left hright
    exact (List.getLast_congr hne happ hsplit).trans
      (List.getLast_append_of_right_ne_nil left right hright)
  have hhead : chunk.head hne = left.head hleft := by
    have happ : left ++ right ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hleft right
    have hcongr : chunk.head hne = (left ++ right).head happ := by
      rw [List.head_eq_getElem, List.head_eq_getElem]
      exact getElem_congr hsplit rfl _
    exact hcongr.trans (List.head_append_of_ne_nil hleft)
  rwa [hlast, hhead] at hcycle

theorem exists_aligned_orbit_chunk_cut
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (left right : List D)
    (hsplit : alignedPermOrderedAllOrbits sigma = left ++ right)
    (hne : alignedPermOrderedAllOrbits sigma ≠ []) :
    exists before cut after cutLeft cutRight,
      alignedPermOrderedAllOrbitLists sigma = before ++ cut :: after /\
        cut = cutLeft ++ cutRight /\
        left = before.flatten ++ cutLeft /\
        right = cutRight ++ after.flatten := by
  have hflatten := flatten_alignedPermOrderedAllOrbitLists sigma
  have hchunks : alignedPermOrderedAllOrbitLists sigma ≠ [] := by
    intro hnil
    rw [hnil] at hflatten
    simp at hflatten
    exact hne hflatten
  apply exists_aligned_chunk_split_of_flatten_eq_append
    (alignedPermOrderedAllOrbitLists sigma) hchunks
    (alignedPermOrderedAllOrbitLists_chunk_ne_nil sigma) left right
  rw [hflatten]
  exact hsplit

set_option maxHeartbeats 800000 in

theorem sum_map_permOrderedAllCycles_eq_support_aligned
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (f : D -> Int) :
    ((permOrderedAllCycles sigma).map f).sum =
      ∑ d ∈ sigma.support, f d := by
  classical
  unfold permOrderedAllCycles
  rw [sum_map_list_flatMap, sum_map_finset_toList]
  have hone : (∑ cycle ∈ sigma.cycleFactorsFinset,
      ((if hcycle : cycle ∈ sigma.cycleFactorsFinset then
          permOrderedCycleFactor sigma cycle hcycle else []).map f).sum) =
      ∑ cycle ∈ sigma.cycleFactorsFinset,
        ∑ d ∈ cycle.support, f d := by
    apply Finset.sum_congr rfl
    intro cycle hcycle
    rw [dif_pos hcycle, sum_map_permOrderedCycleFactor]
  rw [hone]
  have hdisjoint :
      (↑sigma.cycleFactorsFinset : Set (Equiv.Perm D)).PairwiseDisjoint
        (fun cycle => cycle.support) := by
    intro c hc d hd hcd
    exact (sigma.cycleFactorsFinset_pairwise_disjoint
      hc hd hcd).disjoint_support
  have hunion : sigma.cycleFactorsFinset.biUnion
      (fun cycle => cycle.support) = sigma.support := by
    ext d
    rw [Finset.mem_biUnion]
    exact Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.symm
  rw [<- Finset.sum_biUnion hdisjoint, hunion]

theorem sum_map_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (f : D -> Int) :
    ((alignedPermOrderedAllOrbits sigma).map f).sum = ∑ d, f d := by
  classical
  rw [alignedPermOrderedAllOrbits, List.map_append, List.sum_append,
    sum_map_permOrderedAllCycles_eq_support_aligned]
  unfold alignedPermOrderedFixedPoints
  rw [sum_map_finset_toList]
  let fixed : Finset D := Finset.univ.filter fun d => sigma d = d
  have hdisjoint : Disjoint sigma.support fixed := by
    rw [Finset.disjoint_left]
    intro d hsupport hfixed
    have hne := Equiv.Perm.mem_support.mp hsupport
    have heq : sigma d = d := by simpa [fixed] using hfixed
    exact hne heq
  have hunion : sigma.support ∪ fixed = Finset.univ := by
    ext d
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases h : sigma d = d
    · exact Or.inr (by simp [fixed, h])
    · exact Or.inl (Equiv.Perm.mem_support.mpr h)
  change (∑ d ∈ sigma.support, f d) + ∑ d ∈ fixed, f d = _
  rw [<- Finset.sum_union hdisjoint, hunion]

theorem mem_permOrderedCycleFactor_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset) (d : D) :
    d ∈ permOrderedCycleFactor sigma cycle hcycle ↔
      d ∈ cycle.support := by
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  let enumerate := permCycleFinEquivSupport cycle hc seed
  rw [show permOrderedCycleFactor sigma cycle hcycle =
      List.ofFn (fun k => (enumerate k).1) by rfl]
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    rw [← hi]
    exact (enumerate i).2
  · intro hd
    obtain ⟨i, hi⟩ := enumerate.surjective ⟨d, hd⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem mem_permOrderedAllCycles_iff_support
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (d : D) :
    d ∈ permOrderedAllCycles sigma ↔ d ∈ sigma.support := by
  classical
  rw [permOrderedAllCycles, List.mem_flatMap]
  constructor
  · rintro ⟨cycle, hcycleList, hd⟩
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    rw [dif_pos hcycle,
      mem_permOrderedCycleFactor_iff sigma cycle hcycle d] at hd
    exact
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mpr
        ⟨cycle, hcycle, hd⟩
  · intro hd
    obtain ⟨cycle, hcycle, hdcycle⟩ :=
      Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp hd
    refine ⟨cycle, by simpa, ?_⟩
    rw [dif_pos hcycle,
      mem_permOrderedCycleFactor_iff sigma cycle hcycle d]
    exact hdcycle

theorem mem_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (d : D) :
    d ∈ alignedPermOrderedAllOrbits sigma := by
  classical
  rw [alignedPermOrderedAllOrbits, List.mem_append]
  by_cases hfixed : sigma d = d
  · right
    simp [alignedPermOrderedFixedPoints, hfixed]
  · left
    rw [mem_permOrderedAllCycles_iff_support]
    exact Equiv.Perm.mem_support.mpr hfixed

theorem length_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedAllOrbits sigma).length = Fintype.card D := by
  have hsum := sum_map_alignedPermOrderedAllOrbits sigma
    (Function.const D (1 : Int))
  have hone (items : List D) :
      (items.map (Function.const D (1 : Int))).sum =
        (items.length : Int) := by
    induction items with
    | nil => simp
    | cons d items ih =>
        simp only [List.map_cons, List.sum_cons, Function.const_apply,
          List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [ih]
        omega
  rw [hone] at hsum
  have hsum' : ((alignedPermOrderedAllOrbits sigma).length : Int) =
      (Fintype.card D : Int) := by
    simpa using hsum
  exact Int.ofNat_inj.mp hsum'

theorem alignedPermOrderedAllOrbits_nodup
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) :
    (alignedPermOrderedAllOrbits sigma).Nodup := by
  classical
  change ((↑(alignedPermOrderedAllOrbits sigma) : Multiset D)).Nodup
  rw [← Multiset.dedup_card_eq_card_iff_nodup]
  change (alignedPermOrderedAllOrbits sigma).toFinset.card =
    (alignedPermOrderedAllOrbits sigma).length
  rw [show (alignedPermOrderedAllOrbits sigma).toFinset = Finset.univ by
    ext d
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact mem_alignedPermOrderedAllOrbits sigma d]
  simp [length_alignedPermOrderedAllOrbits]

theorem alignedPermOrderedAllOrbitLists_chunk_nodup
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma) :
    chunk.Nodup := by
  have hall : (alignedPermOrderedAllOrbitLists sigma).flatten.Nodup := by
    rw [flatten_alignedPermOrderedAllOrbitLists]
    exact alignedPermOrderedAllOrbits_nodup sigma
  exact (List.nodup_flatten.mp hall).1 chunk hchunk


theorem alignedPermOrderedAllOrbitLists_sameCycle_of_mem
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    {x y : D} (hx : x ∈ chunk) (hy : y ∈ chunk) :
    sigma.SameCycle x y := by
  rw [alignedPermOrderedAllOrbitLists, List.mem_append] at hchunk
  rcases hchunk with hfactor | hfixed
  · rw [alignedPermOrderedCycleFactorLists] at hfactor
    obtain ⟨cycle, hcycleList, hchunk⟩ := List.mem_map.mp hfactor
    have hcycle : cycle ∈ sigma.cycleFactorsFinset := by
      simpa using hcycleList
    subst chunk
    simp only [dif_pos hcycle] at hx hy
    have hxSupport :=
      (mem_permOrderedCycleFactor_iff sigma cycle hcycle x).mp hx
    have hySupport :=
      (mem_permOrderedCycleFactor_iff sigma cycle hcycle y).mp hy
    exact (Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset
      hcycle).2 hxSupport hySupport
  · obtain ⟨d, hd, hchunk⟩ := List.mem_map.mp hfixed
    subst chunk
    simp only [List.mem_singleton] at hx hy
    exact (hx.trans hy.symm).sameCycle sigma



theorem alignedPermOrderedAllOrbitLists_prefix_mem_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (parts suffix : List (List D))
    (hall : alignedPermOrderedAllOrbitLists sigma = parts ++ suffix)
    (x : D) :
    sigma x ∈ parts.flatten <-> x ∈ parts.flatten := by
  constructor
  · rw [List.mem_flatten, List.mem_flatten]
    rintro ⟨part, hpart, hsigma⟩
    refine ⟨part, hpart, ?_⟩
    apply (alignedPermOrderedAllOrbitLists_mem_iff sigma part ?_ x).mp hsigma
    rw [hall]
    simp [hpart]
  · rw [List.mem_flatten, List.mem_flatten]
    rintro ⟨part, hpart, hx⟩
    refine ⟨part, hpart, ?_⟩
    apply (alignedPermOrderedAllOrbitLists_mem_iff sigma part ?_ x).mpr hx
    rw [hall]
    simp [hpart]

theorem alignedPermOrderedOrbitChunk_mem_left_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (chunk left right : List D)
    (hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ [])
    (x : D) :
    sigma x ∈ left ↔
      (x ∈ left ∧ x ≠ left.getLast hleft) ∨
        x = right.getLast hright := by
  have hchunkNodup :=
    alignedPermOrderedAllOrbitLists_chunk_nodup sigma chunk hchunk
  have happNodup : (left ++ right).Nodup := by
    simpa [hsplit] using hchunkNodup
  have hdisjoint := (List.nodup_append.mp happNodup).2.2
  constructor
  · intro hsx
    have hsChunk : sigma x ∈ chunk := by
      rw [hsplit, List.mem_append]
      exact Or.inl hsx
    have hxChunk :=
      (alignedPermOrderedAllOrbitLists_mem_iff
        sigma chunk hchunk x).mp hsChunk
    rw [hsplit, List.mem_append] at hxChunk
    rcases hxChunk with hxLeft | hxRight
    · by_cases hxLast : x = left.getLast hleft
      · have hboundary := alignedPermOrderedOrbitChunk_split_boundary
          sigma chunk left right hchunk hsplit hleft hright
        have heq : sigma x = right.head hright := by
          simpa [hxLast] using hboundary
        have hneq := hdisjoint (sigma x) hsx
          (right.head hright) (List.head_mem hright)
        exact False.elim (hneq heq)
      · exact Or.inl ⟨hxLeft, hxLast⟩
    · by_cases hxLast : x = right.getLast hright
      · exact Or.inr hxLast
      · have hsRight :=
          alignedPermOrderedOrbitChunk_right_forward_of_ne_last
            sigma chunk left right hchunk hsplit hright
            x hxRight hxLast
        have hneq := hdisjoint (sigma x) hsx (sigma x) hsRight
        exact False.elim (hneq rfl)
  · rintro (⟨hxLeft, hxLast⟩ | rfl)
    · exact alignedPermOrderedOrbitChunk_left_forward_of_ne_last
        sigma chunk left right hchunk hsplit hleft
        x hxLeft hxLast
    · rw [alignedPermOrderedOrbitChunk_split_entry_boundary
        sigma chunk left right hchunk hsplit hleft hright]
      exact List.head_mem hleft

theorem alignedPermOrderedOrbitPrefix_mem_iff
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D)
    (before : List (List D)) (chunk : List D) (after : List (List D))
    (left right : List D)
    (hall : alignedPermOrderedAllOrbitLists sigma =
      before ++ chunk :: after)
    (hsplit : chunk = left ++ right)
    (hleft : left ≠ []) (hright : right ≠ [])
    (x : D) :
    sigma x ∈ before.flatten ++ left ↔
      (x ∈ before.flatten ++ left ∧ x ≠ left.getLast hleft) ∨
        x = right.getLast hright := by
  have hbefore (y : D) :
      sigma y ∈ before.flatten ↔ y ∈ before.flatten := by
    constructor
    · rw [List.mem_flatten, List.mem_flatten]
      rintro ⟨part, hpart, hsigma⟩
      refine ⟨part, hpart, ?_⟩
      apply (alignedPermOrderedAllOrbitLists_mem_iff
        sigma part ?_ y).mp hsigma
      rw [hall]
      simp [hpart]
    · rw [List.mem_flatten, List.mem_flatten]
      rintro ⟨part, hpart, hy⟩
      refine ⟨part, hpart, ?_⟩
      apply (alignedPermOrderedAllOrbitLists_mem_iff
        sigma part ?_ y).mpr hy
      rw [hall]
      simp [hpart]
  have hchunk : chunk ∈ alignedPermOrderedAllOrbitLists sigma := by
    rw [hall]
    simp
  have hflatNodup :
      (alignedPermOrderedAllOrbitLists sigma).flatten.Nodup := by
    rw [flatten_alignedPermOrderedAllOrbitLists]
    exact alignedPermOrderedAllOrbits_nodup sigma
  have hprefixNodup : (before.flatten ++ chunk).Nodup := by
    rw [hall, List.flatten_append, List.flatten_cons] at hflatNodup
    have hreassoc :
        ((before.flatten ++ chunk) ++ after.flatten).Nodup := by
      simpa [List.append_assoc] using hflatNodup
    exact hreassoc.of_append_left
  have hdisjoint : before.flatten.Disjoint chunk := by
    rw [List.disjoint_left]
    intro a ha hac
    exact (List.nodup_append.mp hprefixNodup).2.2 a ha a hac rfl
  rw [List.mem_append, List.mem_append]
  constructor
  · rintro (hsBefore | hsLeft)
    · have hxBefore := (hbefore x).mp hsBefore
      refine Or.inl ⟨Or.inl hxBefore, ?_⟩
      intro hxLast
      apply hdisjoint hxBefore
      rw [hsplit, List.mem_append]
      exact Or.inl (hxLast ▸ List.getLast_mem hleft)
    · rcases (alignedPermOrderedOrbitChunk_mem_left_iff
          sigma chunk left right hchunk hsplit hleft hright x).mp hsLeft with
        ⟨hxLeft, hxLast⟩ | hxEntry
      · exact Or.inl ⟨Or.inr hxLeft, hxLast⟩
      · exact Or.inr hxEntry
  · rintro (⟨hxSelected, hxLast⟩ | hxEntry)
    · rcases hxSelected with hxBefore | hxLeft
      · exact Or.inl ((hbefore x).mpr hxBefore)
      · exact Or.inr
          ((alignedPermOrderedOrbitChunk_mem_left_iff
            sigma chunk left right hchunk hsplit hleft hright x).mpr
              (Or.inl ⟨hxLeft, hxLast⟩))
    · exact Or.inr
        ((alignedPermOrderedOrbitChunk_mem_left_iff
          sigma chunk left right hchunk hsplit hleft hright x).mpr
            (Or.inr hxEntry))

theorem exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned
    {A : Type*} (items : List A) (step : A -> Int)
    (hsteps : forall x, x ∈ items ->
      step x = 0 \/ step x = 1 \/ step x = -1)
    (target total : Int) (hsum : (items.map step).sum = total)
    (htarget_nonneg : 0 <= target) (htarget_le : target <= total) :
    exists pre suf : List A,
      items = pre ++ suf /\ (pre.map step).sum = target := by
  induction items generalizing target total with
  | nil =>
      have htarget : target = 0 := by
        simp only [List.map_nil, List.sum_nil] at hsum
        omega
      exact ⟨[], [], rfl, by simp [htarget]⟩
  | cons x items ih =>
      have hx := hsteps x (by simp)
      have htail : forall y, y ∈ items ->
          step y = 0 \/ step y = 1 \/ step y = -1 := by
        intro y hy
        exact hsteps y (by simp [hy])
      by_cases htarget : target = 0
      · exact ⟨[], x :: items, by simp, by simp [htarget]⟩
      · have htarget_pos : 0 < target := by omega
        rcases hx with hx | hx | hx
        · have htailSum : (items.map step).sum = total := by
            simp only [List.map_cons, List.sum_cons, hx, zero_add] at *
            assumption
          obtain ⟨pre, suf, hsplit, hprefix⟩ :=
            ih htail target total htailSum htarget_nonneg htarget_le
          exact ⟨x :: pre, suf, by simp [hsplit], by simp [hx, hprefix]⟩
        · have htailSum : (items.map step).sum = total - 1 := by
            simp only [List.map_cons, List.sum_cons, hx] at *
            omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ := ih htail
            (target - 1) (total - 1) htailSum (by omega) (by omega)
          exact ⟨x :: pre, suf, by simp [hsplit], by simp [hx, hprefix]⟩
        · have htailSum : (items.map step).sum = total + 1 := by
            simp only [List.map_cons, List.sum_cons, hx] at *
            omega
          obtain ⟨pre, suf, hsplit, hprefix⟩ := ih htail
            (target + 1) (total + 1) htailSum (by omega) (by omega)
          exact ⟨x :: pre, suf, by simp [hsplit], by simp [hx, hprefix]⟩

theorem exists_two_unit_blocks_of_alignedPermOrderedAllOrbits
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma : Equiv.Perm D) (step : D -> Int)
    (hsteps : forall d, step d = 0 \/ step d = 1 \/ step d = -1)
    (hsum : ∑ d, step d = 2) :
    exists first second : List D,
      alignedPermOrderedAllOrbits sigma = first ++ second /\
        (first.map step).sum = 1 /\
        (second.map step).sum = 1 := by
  obtain ⟨first, second, hsplit, hfirst⟩ :=
    exists_list_prefix_map_sum_eq_of_zeroOrUnitSteps_aligned
      (alignedPermOrderedAllOrbits sigma) step (fun d hd => hsteps d)
      1 2 (by rw [sum_map_alignedPermOrderedAllOrbits]; exact hsum)
      (by norm_num) (by norm_num)
  refine ⟨first, second, hsplit, hfirst, ?_⟩
  have htotal : ((alignedPermOrderedAllOrbits sigma).map step).sum = 2 := by
    rw [sum_map_alignedPermOrderedAllOrbits]
    exact hsum
  rw [hsplit, List.map_append, List.sum_append, hfirst] at htotal
  omega

noncomputable def doubledAlignedCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) : Int :=
  if x.2 then 0 else
    sixVertexDegreeTwoStrandStepSeamSign hdegree x.1

theorem doubledAlignedCharge_zeroOrUnit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (x : DoubledAlignedState omega eta) :
    doubledAlignedCharge hdegree x = 0 \/
      doubledAlignedCharge hdegree x = 1 \/
      doubledAlignedCharge hdegree x = -1 := by
  rcases x with ⟨d, branch⟩
  cases branch
  · by_cases hzero : sixVertexDegreeTwoStrandStepSeamSign hdegree d = 0
    · exact Or.inl (by simpa [doubledAlignedCharge] using hzero)
    · exact Or.inr (by
        simpa [doubledAlignedCharge] using
          sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d hzero)
  · exact Or.inl (by simp [doubledAlignedCharge])

theorem sum_doubledAlignedCharge
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (hdegree : SixVertexLocallyDegreeTwo omega eta) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
      ∑ branch : Bool,
        doubledAlignedCharge hdegree (d, branch)) =
      ∑ d : SixVertexOrientedDisagreementDart omega eta,
        sixVertexDegreeTwoStrandStepSeamSign hdegree d := by
  classical
  apply Finset.sum_congr rfl
  intro d hd
  simp [doubledAlignedCharge]

theorem sum_doubledAlignedCharge_eq_two
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (∑ d : SixVertexOrientedDisagreementDart omega eta,
      ∑ branch : Bool,
        doubledAlignedCharge hdegree (d, branch)) = 2 := by
  rw [sum_doubledAlignedCharge]
  exact sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two
    homega heta hdegree n homegaSector hetaSector hn

structure DoubledAlignedUnitOrbitSplit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) where
  first : List (DoubledAlignedState omega eta)
  second : List (DoubledAlignedState omega eta)
  split : alignedPermOrderedAllOrbits
      (doubledAlignedFirstReturnPerm homega heta hdegree) = first ++ second
  first_charge : (first.map (doubledAlignedCharge hdegree)).sum = 1
  second_charge : (second.map (doubledAlignedCharge hdegree)).sum = 1

theorem DoubledAlignedUnitOrbitSplit.first_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta)
    (split : DoubledAlignedUnitOrbitSplit homega heta hdegree) :
    split.first.Nodup := by
  have hall := alignedPermOrderedAllOrbits_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
  rw [split.split] at hall
  exact hall.of_append_left

theorem exists_doubledAlignedUnitOrbitSplit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    Nonempty (DoubledAlignedUnitOrbitSplit homega heta hdegree) := by
  obtain ⟨first, second, hsplit, hfirst, hsecond⟩ :=
    exists_two_unit_blocks_of_alignedPermOrderedAllOrbits
      (doubledAlignedFirstReturnPerm homega heta hdegree)
      (doubledAlignedCharge hdegree)
      (doubledAlignedCharge_zeroOrUnit hdegree)
      (by
        rw [Fintype.sum_prod_type]
        exact sum_doubledAlignedCharge_eq_two homega heta hdegree n
          homegaSector hetaSector hn)
  exact ⟨⟨first, second, hsplit, hfirst, hsecond⟩⟩

noncomputable def canonicalDoubledAlignedUnitOrbitSplit
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    DoubledAlignedUnitOrbitSplit homega heta hdegree :=
  Classical.choice (exists_doubledAlignedUnitOrbitSplit
    homega heta hdegree n homegaSector hetaSector hn)

noncomputable def canonicalDoubledAlignedSelectedStates
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) : List (DoubledAlignedState omega eta) :=
  (canonicalDoubledAlignedUnitOrbitSplit homega heta hdegree n
    homegaSector hetaSector hn).first

theorem canonicalDoubledAlignedSelectedStates_nodup
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    (canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn).Nodup :=
  (canonicalDoubledAlignedUnitOrbitSplit homega heta hdegree n
    homegaSector hetaSector hn).first_nodup

noncomputable def canonicalDoubledAlignedBranchMask
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) (branch : Bool) (v : T.Vertex) : Bool :=
  alignedStateListBranchMask homega heta
    (canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn) branch v

theorem exists_canonicalDoubledAlignedOrbitChunkCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    let split := canonicalDoubledAlignedUnitOrbitSplit
      homega heta hdegree n homegaSector hetaSector hn
    exists before cut after cutLeft cutRight,
      alignedPermOrderedAllOrbitLists
          (doubledAlignedFirstReturnPerm homega heta hdegree) =
        before ++ cut :: after /\
      cut = cutLeft ++ cutRight /\
      split.first = before.flatten ++ cutLeft /\
      split.second = cutRight ++ after.flatten := by
  let split := canonicalDoubledAlignedUnitOrbitSplit
    homega heta hdegree n homegaSector hetaSector hn
  have hfirst : split.first ≠ [] := by
    intro hnil
    have hcharge := split.first_charge
    rw [hnil] at hcharge
    simp at hcharge
  have hall : alignedPermOrderedAllOrbits
      (doubledAlignedFirstReturnPerm homega heta hdegree) ≠ [] := by
    rw [split.split]
    intro hnil
    have := congrArg List.length hnil
    simp only [List.length_nil, List.length_append] at this
    have : split.first.length = 0 := by omega
    exact hfirst (List.length_eq_zero_iff.mp this)
  exact exists_aligned_orbit_chunk_cut
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    split.first split.second split.split hall

structure CanonicalDoubledAlignedOrbitChunkCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) where
  before : List (List (DoubledAlignedState omega eta))
  cut : List (DoubledAlignedState omega eta)
  after : List (List (DoubledAlignedState omega eta))
  cutLeft : List (DoubledAlignedState omega eta)
  cutRight : List (DoubledAlignedState omega eta)
  orbitLists : alignedPermOrderedAllOrbitLists
      (doubledAlignedFirstReturnPerm homega heta hdegree) =
    before ++ cut :: after
  cut_eq : cut = cutLeft ++ cutRight
  selected_eq : canonicalDoubledAlignedSelectedStates
      homega heta hdegree n homegaSector hetaSector hn =
    before.flatten ++ cutLeft
  complement_eq :
    (canonicalDoubledAlignedUnitOrbitSplit homega heta hdegree n
      homegaSector hetaSector hn).second =
      cutRight ++ after.flatten

noncomputable def canonicalDoubledAlignedOrbitChunkCut
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn := by
  let hex := exists_canonicalDoubledAlignedOrbitChunkCut
    homega heta hdegree n homegaSector hetaSector hn
  let before := Classical.choose hex
  let hex := Classical.choose_spec hex
  let cut := Classical.choose hex
  let hex := Classical.choose_spec hex
  let after := Classical.choose hex
  let hex := Classical.choose_spec hex
  let cutLeft := Classical.choose hex
  let hex := Classical.choose_spec hex
  let cutRight := Classical.choose hex
  let h := Classical.choose_spec hex
  exact ⟨before, cut, after, cutLeft, cutRight,
    h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem CanonicalDoubledAlignedOrbitChunkCut.cut_mem
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn) :
    cut.cut ∈ alignedPermOrderedAllOrbitLists
      (doubledAlignedFirstReturnPerm homega heta hdegree) := by
  rw [cut.orbitLists]
  simp

theorem CanonicalDoubledAlignedOrbitChunkCut.cutLeft_mem_selected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    {x : DoubledAlignedState omega eta} (hx : x ∈ cut.cutLeft) :
    x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn := by
  rw [cut.selected_eq, List.mem_append]
  exact Or.inr hx

theorem CanonicalDoubledAlignedOrbitChunkCut.cutRight_not_mem_selected
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    {x : DoubledAlignedState omega eta} (hx : x ∈ cut.cutRight) :
    x ∉ canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn := by
  let split := canonicalDoubledAlignedUnitOrbitSplit
    homega heta hdegree n homegaSector hetaSector hn
  have hall := alignedPermOrderedAllOrbits_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
  rw [split.split] at hall
  have hsecond : x ∈ split.second := by
    rw [cut.complement_eq, List.mem_append]
    exact Or.inl hx
  intro hselected
  exact (List.nodup_append.mp hall).2.2 x hselected x hsecond rfl

theorem CanonicalDoubledAlignedOrbitChunkCut.proper_boundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    doubledAlignedFirstReturnPerm homega heta hdegree
        (cut.cutLeft.getLast hleft) =
      cut.cutRight.head hright :=
  alignedPermOrderedOrbitChunk_split_boundary
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cutLeft cut.cutRight (cut.cut_mem)
    cut.cut_eq hleft hright

theorem CanonicalDoubledAlignedOrbitChunkCut.proper_entry_boundary
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    doubledAlignedFirstReturnPerm homega heta hdegree
        (cut.cutRight.getLast hright) =
      cut.cutLeft.head hleft := by
  have hcut : cut.cut ≠ [] := by
    rw [cut.cut_eq]
    exact List.append_ne_nil_of_left_ne_nil hleft cut.cutRight
  have hcycle := alignedPermOrderedAllOrbitLists_getLast
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cut_mem hcut
  have hlast : cut.cut.getLast hcut =
      cut.cutRight.getLast hright := by
    have happ : cut.cutLeft ++ cut.cutRight ≠ [] :=
      List.append_ne_nil_of_right_ne_nil cut.cutLeft hright
    exact (List.getLast_congr hcut happ cut.cut_eq).trans
      (List.getLast_append_of_right_ne_nil
        cut.cutLeft cut.cutRight hright)
  have hhead : cut.cut.head hcut = cut.cutLeft.head hleft := by
    have happ : cut.cutLeft ++ cut.cutRight ≠ [] :=
      List.append_ne_nil_of_left_ne_nil hleft cut.cutRight
    have hcongr : cut.cut.head hcut =
        (cut.cutLeft ++ cut.cutRight).head happ := by
      rw [List.head_eq_getElem, List.head_eq_getElem]
      exact getElem_congr cut.cut_eq rfl _
    exact hcongr.trans (List.head_append_of_ne_nil hleft)
  rw [hlast, hhead] at hcycle
  exact hcycle




theorem CanonicalDoubledAlignedOrbitChunkCut.transition_states_ne
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    cut.cutRight.head hright ≠ cut.cutLeft.head hleft := by
  have hchunkNodup := alignedPermOrderedAllOrbitLists_chunk_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cut_mem
  have happNodup : (cut.cutLeft ++ cut.cutRight).Nodup := by
    simpa [cut.cut_eq] using hchunkNodup
  have hdisjoint : cut.cutLeft.Disjoint cut.cutRight := by
    rw [List.disjoint_left]
    intro a ha hb
    exact ((List.nodup_append.mp happNodup).2.2 a ha a hb) rfl
  intro heq
  apply (List.disjoint_left.mp hdisjoint) (List.head_mem hleft)
  rw [← heq]
  exact List.head_mem hright

theorem CanonicalDoubledAlignedOrbitChunkCut.selected_mem_iff
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ [])
    (x : DoubledAlignedState omega eta) :
    doubledAlignedFirstReturnPerm homega heta hdegree x ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ↔
      (x ∈ canonicalDoubledAlignedSelectedStates
          homega heta hdegree n homegaSector hetaSector hn ∧
        x ≠ cut.cutLeft.getLast hleft) ∨
      x = cut.cutRight.getLast hright := by
  rw [cut.selected_eq]
  exact alignedPermOrderedOrbitPrefix_mem_iff
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.before cut.cut cut.after cut.cutLeft cut.cutRight
    cut.orbitLists cut.cut_eq hleft hright x

theorem CanonicalDoubledAlignedOrbitChunkCut.selected_predecessor_iff_of_ne_heads
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ [])
    (y : DoubledAlignedState omega eta)
    (hneRight : y ≠ cut.cutRight.head hright)
    (hneLeft : y ≠ cut.cutLeft.head hleft) :
    y ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ↔
      (doubledAlignedFirstReturnPerm
        homega heta hdegree).symm y ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn := by
  let sigma := doubledAlignedFirstReturnPerm homega heta hdegree
  let x := sigma.symm y
  have hxRight : x ≠ cut.cutRight.getLast hright := by
    intro hx
    apply hneLeft
    have hentry := cut.proper_entry_boundary
      homega heta hdegree n homegaSector hetaSector hn hleft hright
    change sigma (cut.cutRight.getLast hright) =
      cut.cutLeft.head hleft at hentry
    calc
      y = sigma x := by simp [x, sigma]
      _ = sigma (cut.cutRight.getLast hright) := by rw [hx]
      _ = cut.cutLeft.head hleft := hentry
  have hxLeft : x ≠ cut.cutLeft.getLast hleft := by
    intro hx
    apply hneRight
    have hboundary := cut.proper_boundary
      homega heta hdegree n homegaSector hetaSector hn hleft hright
    change sigma (cut.cutLeft.getLast hleft) =
      cut.cutRight.head hright at hboundary
    calc
      y = sigma x := by simp [x, sigma]
      _ = sigma (cut.cutLeft.getLast hleft) := by rw [hx]
      _ = cut.cutRight.head hright := hboundary
  have hiff := cut.selected_mem_iff homega heta hdegree n
    homegaSector hetaSector hn hleft hright x
  change y ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
        homegaSector hetaSector hn ↔
    x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
      homegaSector hetaSector hn
  rw [show y = sigma x by simp [x, sigma]]
  simpa [sigma, hxLeft, hxRight] using hiff



theorem CanonicalDoubledAlignedOrbitChunkCut.selected_invariant_of_left_empty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft = [])
    (x : DoubledAlignedState omega eta) :
    doubledAlignedFirstReturnPerm homega heta hdegree x ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn <->
      x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
        homegaSector hetaSector hn := by
  rw [cut.selected_eq, hleft, List.append_nil]
  apply alignedPermOrderedAllOrbitLists_prefix_mem_iff
    (doubledAlignedFirstReturnPerm homega heta hdegree) cut.before
    (cut.cut :: cut.after)
  simpa using cut.orbitLists



theorem CanonicalDoubledAlignedOrbitChunkCut.selected_invariant_of_right_empty
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hright : cut.cutRight = [])
    (x : DoubledAlignedState omega eta) :
    doubledAlignedFirstReturnPerm homega heta hdegree x ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn <->
      x ∈ canonicalDoubledAlignedSelectedStates homega heta hdegree n
        homegaSector hetaSector hn := by
  have hcut : cut.cut = cut.cutLeft := by
    simpa [hright] using cut.cut_eq
  rw [cut.selected_eq, ← hcut]
  have hinvariant := alignedPermOrderedAllOrbitLists_prefix_mem_iff
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    (cut.before ++ [cut.cut]) cut.after (by simpa using cut.orbitLists) x
  simpa [List.flatten_append] using hinvariant

theorem CanonicalDoubledAlignedOrbitChunkCut.rightHead_transition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    cut.cutRight.head hright ∉
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ∧
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutRight.head hright) ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn := by
  constructor
  · exact cut.cutRight_not_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.head_mem hright)
  · have hprev : (doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (cut.cutRight.head hright) = cut.cutLeft.getLast hleft := by
      apply (doubledAlignedFirstReturnPerm homega heta hdegree).injective
      simp only [Equiv.apply_symm_apply]
      exact (cut.proper_boundary homega heta hdegree n homegaSector
        hetaSector hn hleft hright).symm
    rw [hprev]
    exact cut.cutLeft_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.getLast_mem hleft)

theorem CanonicalDoubledAlignedOrbitChunkCut.leftHead_transition
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    cut.cutLeft.head hleft ∈
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn ∧
      (doubledAlignedFirstReturnPerm homega heta hdegree).symm
          (cut.cutLeft.head hleft) ∉
        canonicalDoubledAlignedSelectedStates homega heta hdegree n
          homegaSector hetaSector hn := by
  constructor
  · exact cut.cutLeft_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.head_mem hleft)
  · have hprev : (doubledAlignedFirstReturnPerm homega heta hdegree).symm
        (cut.cutLeft.head hleft) = cut.cutRight.getLast hright := by
      apply (doubledAlignedFirstReturnPerm homega heta hdegree).injective
      simp only [Equiv.apply_symm_apply]
      exact (cut.proper_entry_boundary homega heta hdegree n homegaSector
        hetaSector hn hleft hright).symm
    rw [hprev]
    exact cut.cutRight_not_mem_selected homega heta hdegree n
      homegaSector hetaSector hn (List.getLast_mem hright)

theorem CanonicalDoubledAlignedOrbitChunkCut.not_selected_invariant
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n)
    (cut : CanonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn)
    (hleft : cut.cutLeft ≠ []) (hright : cut.cutRight ≠ []) :
    ¬ forall x : DoubledAlignedState omega eta,
      (doubledAlignedFirstReturnPerm homega heta hdegree x ∈
          canonicalDoubledAlignedSelectedStates
            homega heta hdegree n homegaSector hetaSector hn ↔
        x ∈ canonicalDoubledAlignedSelectedStates
          homega heta hdegree n homegaSector hetaSector hn) := by
  intro hinvariant
  let x := cut.cutLeft.getLast hleft
  have hx : x ∈ canonicalDoubledAlignedSelectedStates
      homega heta hdegree n homegaSector hetaSector hn := by
    rw [cut.selected_eq, List.mem_append]
    exact Or.inr (List.getLast_mem hleft)
  have hchunkNodup := alignedPermOrderedAllOrbitLists_chunk_nodup
    (doubledAlignedFirstReturnPerm homega heta hdegree)
    cut.cut cut.cut_mem
  have happNodup : (cut.cutLeft ++ cut.cutRight).Nodup := by
    simpa [cut.cut_eq] using hchunkNodup
  have hdisjoint : cut.cutLeft.Disjoint cut.cutRight := by
    rw [List.disjoint_left]
    intro a ha hb
    exact ((List.nodup_append.mp happNodup).2.2 a ha a hb) rfl
  have hne : x ≠ cut.cutRight.getLast hright := by
    intro heq
    apply (List.disjoint_left.mp hdisjoint) (List.getLast_mem hleft)
    have heq' : cut.cutLeft.getLast hleft =
        cut.cutRight.getLast hright := heq
    rw [heq']
    exact List.getLast_mem hright
  have hexit : doubledAlignedFirstReturnPerm homega heta hdegree x ∉
      canonicalDoubledAlignedSelectedStates
        homega heta hdegree n homegaSector hetaSector hn := by
    rw [CanonicalDoubledAlignedOrbitChunkCut.selected_mem_iff
      homega heta hdegree n homegaSector hetaSector hn
      cut hleft hright x]
    simp [x, hne]
  exact hexit ((hinvariant x).mpr hx)

theorem canonicalDoubledAlignedOrbitChunkCut_cases
    {T : EvenTorus} {omega eta : SixVertexArrows T}
    (homega : omega.IceRule) (heta : eta.IceRule)
    (hdegree : SixVertexLocallyDegreeTwo omega eta) (n : Nat)
    (homegaSector : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
    (hetaSector : sixVertexUpCount
      (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
    (hn : 0 < n) :
    let cut := canonicalDoubledAlignedOrbitChunkCut homega heta hdegree n
      homegaSector hetaSector hn
    cut.cutLeft = [] ∨ cut.cutRight = [] ∨
      (cut.cutLeft ≠ [] ∧ cut.cutRight ≠ []) := by
  dsimp
  by_cases hleft : (canonicalDoubledAlignedOrbitChunkCut
      homega heta hdegree n homegaSector hetaSector hn).cutLeft = []
  · exact Or.inl hleft
  · by_cases hright : (canonicalDoubledAlignedOrbitChunkCut
        homega heta hdegree n homegaSector hetaSector hn).cutRight = []
    · exact Or.inr (Or.inl hright)
    · exact Or.inr (Or.inr ⟨hleft, hright⟩)





namespace FourByTwoPrefixBondAudit

local instance (arrows : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable arrows.IceRule :=
  inferInstanceAs (Decidable (forall v, arrows.incomingCount v = 2))

local instance (first second : SixVertexArrows sixVertexFourByTwoTorus) :
    Decidable (SixVertexLocallyDegreeTwo first second) := by
  unfold SixVertexLocallyDegreeTwo
  infer_instance

def arrowsOfMask (mask : Nat) :
    SixVertexArrows sixVertexFourByTwoTorus where
  horizontal v := Nat.testBit mask (v.2.val * 4 + v.1.val)
  vertical v := Nat.testBit mask (8 + v.2.val * 4 + v.1.val)

def omega : SixVertexArrows sixVertexFourByTwoTorus := arrowsOfMask 255
def eta : SixVertexArrows sixVertexFourByTwoTorus := arrowsOfMask 23205

def cutVertex : sixVertexFourByTwoTorus.Vertex :=
  sixVertexFourByTwoVertex 0 0

def singletonPrefixLocalPair
    (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  if v = cutVertex then
    exchangeLocalAlignedMask true false false false
      (sixVertexLocalIncomingPattern omega v)
      (sixVertexLocalIncomingPattern eta v)
  else
    (sixVertexLocalIncomingPattern omega v,
      sixVertexLocalIncomingPattern eta v)

def singletonPrefixPattern
    (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern :=
  if layer then (singletonPrefixLocalPair v).2
  else (singletonPrefixLocalPair v).1

theorem omega_ice : omega.IceRule := by decide

theorem eta_ice : eta.IceRule := by decide

theorem locallyDegreeTwo : SixVertexLocallyDegreeTwo omega eta := by decide

theorem cutVertex_alignedRetie_premises :
    let p := sixVertexLocalIncomingPattern omega cutVertex
    let q := sixVertexLocalIncomingPattern eta cutVertex
    p.Ice /\ q.Ice /\
      (sixVertexLocalDisagreementSides p q).card = 2 /\
      compatible true p /\ compatible true q /\
      p (0 : Fin 4) != q (0 : Fin 4) /\
      p (localMate true (localMate true (0 : Fin 4))) !=
        q (localMate true (localMate true (0 : Fin 4))) := by
  decide

theorem singletonPrefix_west_bond_failure :
    singletonPrefixPattern false cutVertex 0 =
      singletonPrefixPattern false
        (SixVertexArrows.cyclicPred
          sixVertexFourByTwoTorus.width_pos cutVertex.1, cutVertex.2) 1 := by
  decide

theorem singletonPrefix_not_bondConsistent :
    Not ((forall (layer : Bool)
        (v : sixVertexFourByTwoTorus.Vertex),
      singletonPrefixPattern layer v 0 =
        !singletonPrefixPattern layer
          (SixVertexArrows.cyclicPred
            sixVertexFourByTwoTorus.width_pos v.1, v.2) 1) /\
      (forall (layer : Bool)
        (v : sixVertexFourByTwoTorus.Vertex),
      singletonPrefixPattern layer v 2 =
        !singletonPrefixPattern layer
          (v.1, SixVertexArrows.cyclicPred
            sixVertexFourByTwoTorus.height_pos v.2) 3)) := by
  decide

def alignedSlot (v : sixVertexFourByTwoTorus.Vertex) : Bool :=
  decide ((v.1.val + v.2.val) % 2 = 1)

def maskedLocalPair
    (select0 select1 : sixVertexFourByTwoTorus.Vertex -> Bool)
    (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern × SixVertexLocalIncomingPattern :=
  exchangeLocalAlignedMask (select0 v) (select1 v)
    (alignedSlot v) (alignedSlot v)
    (sixVertexLocalIncomingPattern omega v)
    (sixVertexLocalIncomingPattern eta v)

def maskedPattern
    (select0 select1 : sixVertexFourByTwoTorus.Vertex -> Bool)
    (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex) :
    SixVertexLocalIncomingPattern :=
  if layer then (maskedLocalPair select0 select1 v).2
  else (maskedLocalPair select0 select1 v).1

def MaskedBondConsistent
    (select0 select1 : sixVertexFourByTwoTorus.Vertex -> Bool) : Prop :=
  (forall (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex),
    maskedPattern select0 select1 layer v 0 =
      !maskedPattern select0 select1 layer
        (SixVertexArrows.cyclicPred
          sixVertexFourByTwoTorus.width_pos v.1, v.2) 1) /\
  (forall (layer : Bool) (v : sixVertexFourByTwoTorus.Vertex),
    maskedPattern select0 select1 layer v 2 =
      !maskedPattern select0 select1 layer
        (v.1, SixVertexArrows.cyclicPred
          sixVertexFourByTwoTorus.height_pos v.2) 3)



def selectorCharge
    (select0 : sixVertexFourByTwoTorus.Vertex -> Bool) : Nat :=
  (select0 (sixVertexFourByTwoVertex 0 0)).toNat +
    (select0 (sixVertexFourByTwoVertex 2 0)).toNat

end FourByTwoPrefixBondAudit

end StatMech.FrontierD
