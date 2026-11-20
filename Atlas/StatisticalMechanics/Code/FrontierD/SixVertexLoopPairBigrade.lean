/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexColoredStrandSplice
import Code.FrontierD.SixVertexMarkedPairLoopFiber










namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropLoopPairBigrade (p : Prop) : Decidable p :=
  Classical.propDecidable p



def sixVertexArrowPairStrandSlotColor
    {T : EvenTorus} (omega eta : SixVertexArrows T)
    (slot : FKLayeredStrandSlot T) : Bool :=
  let arrows := if slot.1 then eta else omega
  if slot.2.2 then
    fkMedialCheckerColor (slot.2.1, .east) ^^
      fkMedialDartIncoming arrows (slot.2.1, .east)
  else
    fkMedialCheckerColor (slot.2.1, .west) ^^
      fkMedialDartIncoming arrows (slot.2.1, .west)

def sixVertexArrowPairTrueStrandSlotCount
    {T : EvenTorus} (omega eta : SixVertexArrows T) : Nat :=
  Fintype.card {slot : FKLayeredStrandSlot T //
    sixVertexArrowPairStrandSlotColor omega eta slot = true}


def sixVertexConfigurationPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) : Nat × Nat :=
  (sixVertexConfigurationPairTotalC pair,
    sixVertexArrowPairTrueStrandSlotCount pair.1.1 pair.2.1)



def sixVertexLoopDecoratedPairColored
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    FKColoredLoopPairingPair T
  | false => decorated.2.1.toColored
  | true => decorated.2.2.toColored

@[simp] theorem sixVertexLoopDecoratedPairColored_false_arrows
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    (sixVertexLoopDecoratedPairColored decorated false).arrows =
      decorated.1.1.1 :=
  SixVertexCompatibleLoopPairing.toColored_arrows _

@[simp] theorem sixVertexLoopDecoratedPairColored_true_arrows
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    (sixVertexLoopDecoratedPairColored decorated true).arrows =
      decorated.1.2.1 :=
  SixVertexCompatibleLoopPairing.toColored_arrows _

theorem sixVertexLoopDecoratedPairColored_totalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    fkColoredLoopPairingPairTotalC
        (sixVertexLoopDecoratedPairColored decorated) =
      sixVertexLoopDecoratedPairTotalC decorated := by
  simp [fkColoredLoopPairingPairTotalC,
    sixVertexLoopDecoratedPairTotalC,
    sixVertexConfigurationPairTotalC]

theorem sixVertexLoopDecoratedPairColored_slotColor
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor
        (sixVertexLoopDecoratedPairColored decorated) slot =
      sixVertexArrowPairStrandSlotColor
        decorated.1.1.1 decorated.1.2.1 slot := by
  rcases slot with ⟨layer, v, side⟩
  cases layer <;> cases side <;> rfl

theorem sixVertexLoopDecoratedPairColored_trueSlotCount
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    fkColoredTrueStrandSlotCount
        (sixVertexLoopDecoratedPairColored decorated) =
      sixVertexArrowPairTrueStrandSlotCount
        decorated.1.1.1 decorated.1.2.1 := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro slot
  change (fkColoredLayeredSlotColor
      (sixVertexLoopDecoratedPairColored decorated) slot = true) ↔ _
  simp [sixVertexLoopDecoratedPairColored_slotColor]


def sixVertexLoopDecoratedPairBigrade
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) : Nat × Nat :=
  (sixVertexLoopDecoratedPairTotalC decorated,
    fkColoredTrueStrandSlotCount
      (sixVertexLoopDecoratedPairColored decorated))

theorem sixVertexLoopDecoratedPairBigrade_eq_configurationPair
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    sixVertexLoopDecoratedPairBigrade decorated =
      sixVertexConfigurationPairBigrade decorated.1 := by
  apply Prod.ext
  · rfl
  · exact sixVertexLoopDecoratedPairColored_trueSlotCount decorated

theorem sixVertexLoopDecoratedPairBigrade_eq_colored
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) :
    sixVertexLoopDecoratedPairBigrade decorated =
      (fkColoredLoopPairingPairTotalC
          (sixVertexLoopDecoratedPairColored decorated),
        fkColoredTrueStrandSlotCount
          (sixVertexLoopDecoratedPairColored decorated)) := by
  unfold sixVertexLoopDecoratedPairBigrade
  rw [sixVertexLoopDecoratedPairColored_totalC]

end

end StatMech.FrontierD
