/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexRoutedUnitFineRelation











namespace StatMech.FrontierD

noncomputable section


def fkColoredLoopPairingPairSwapLayers
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    FKColoredLoopPairingPair T :=
  fun layer => source (!layer)

@[simp] theorem fkColoredLoopPairingPairSwapLayers_apply
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) (layer : Bool) :
    fkColoredLoopPairingPairSwapLayers source layer = source (!layer) := rfl

@[simp] theorem fkColoredLoopPairingPairSwapLayers_swap
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredLoopPairingPairSwapLayers
        (fkColoredLoopPairingPairSwapLayers source) = source := by
  funext layer
  cases layer <;> rfl


def fkColoredLayeredStrandSlotSwapLayers
    {T : EvenTorus} : Equiv.Perm (FKLayeredStrandSlot T) where
  toFun slot := (!slot.1, slot.2)
  invFun slot := (!slot.1, slot.2)
  left_inv slot := by rcases slot with ⟨layer, slot⟩; cases layer <;> rfl
  right_inv slot := by rcases slot with ⟨layer, slot⟩; cases layer <;> rfl

@[simp] theorem fkColoredLoopPairingPairSwapLayers_slotColor
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (slot : FKLayeredStrandSlot T) :
    fkColoredLayeredSlotColor (fkColoredLoopPairingPairSwapLayers source) slot =
      fkColoredLayeredSlotColor source
        (fkColoredLayeredStrandSlotSwapLayers slot) := by
  rcases slot with ⟨layer, vertex, side⟩
  cases layer <;> rfl


theorem fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredTrueStrandSlotCount
        (fkColoredLoopPairingPairSwapLayers source) =
      fkColoredTrueStrandSlotCount source := by
  unfold fkColoredTrueStrandSlotCount
  apply Fintype.card_congr
  apply Equiv.subtypeEquiv fkColoredLayeredStrandSlotSwapLayers
  intro slot
  rw [fkColoredLoopPairingPairSwapLayers_slotColor]


@[simp] theorem fkColoredLoopPairingPairSwapLayers_totalC
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) :
    fkColoredLoopPairingPairTotalC
        (fkColoredLoopPairingPairSwapLayers source) =
      fkColoredLoopPairingPairTotalC source := by
  simp [fkColoredLoopPairingPairTotalC,
    fkColoredLoopPairingPairSwapLayers, add_comm]


theorem sixVertexPairAtMostTwoCycleRelated_swap_target
    {T : EvenTorus}
    {source target : SixVertexArrows T × SixVertexArrows T}
    (hrelated : sixVertexPairAtMostTwoCycleRelated source target) :
    sixVertexPairAtMostTwoCycleRelated source (target.2, target.1) := by
  rcases target with ⟨targetFirst, targetSecond⟩
  rcases hrelated with ⟨family, sign, hhorizontal, hvertical⟩
  refine ⟨family, sign, ?_, ?_⟩
  · rw [← hhorizontal]
    funext v
    unfold sixVertexPairUnionHorizontalDelta sixVertexPairUnionHorizontal
    simp only
    omega
  · rw [← hvertical]
    funext v
    unfold sixVertexPairUnionVerticalDelta sixVertexPairUnionVertical
    simp only
    omega




structure FKColoredFineTwoCycleUnitTransferSpliceKey
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) where
  splice : FKColoredStrandSplice source
  preservesTotalC : splice.PreservesTotalC
  seamDelta_false : splice.seamDelta false = 1
  seamDelta_true : splice.seamDelta true = -1
  fine :
    sixVertexHorizontalPairBoundedFineRowProfile
        ((splice.target false).arrows.horizontal,
          (splice.target true).arrows.horizontal) =
      sixVertexHorizontalPairBoundedFineRowProfile
        ((source false).arrows.horizontal,
          (source true).arrows.horizontal)
  twoCycle :
    sixVertexPairAtMostTwoCycleRelated
      ((source false).arrows, (source true).arrows)
      ((splice.target false).arrows, (splice.target true).arrows)

namespace FKColoredFineTwoCycleUnitTransferSpliceKey


def ofRoutedKey
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferRoutedKey source) :
    FKColoredFineTwoCycleUnitTransferSpliceKey source where
  splice := key.splice
  preservesTotalC := key.toFKColoredUnitTransferRoutedKey.preservesTotalC
  seamDelta_false := key.toFKColoredUnitTransferRoutedKey.seamDelta_false
  seamDelta_true := key.toFKColoredUnitTransferRoutedKey.seamDelta_true
  fine := key.fine
  twoCycle := key.twoCycle


@[simp] theorem recovers_source
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    key.splice.symm.target = source :=
  key.splice.symm_target


theorem target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    (fkColoredLoopPairingPairTotalC key.splice.target,
        fkColoredTrueStrandSlotCount key.splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) :=
  key.splice.target_bigrade key.preservesTotalC


theorem target_twoCycleFine
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    sixVertexPairAtMostTwoCycleFineRelated
      ((source false).arrows, (source true).arrows)
      ((key.splice.target false).arrows,
        (key.splice.target true).arrows) :=
  ⟨key.twoCycle, key.fine.symm⟩


noncomputable def swapSplice
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    FKColoredStrandSplice source := by
  let swapped := fkColoredLoopPairingPairSwapLayers key.splice.target
  have hcount : fkColoredTrueStrandSlotCount source =
      fkColoredTrueStrandSlotCount swapped := by
    exact (fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount
      key.splice.target).trans key.splice.target_trueStrandSlotCount |>.symm
  exact FKColoredStrandSplice.ofColorEquiv source swapped
    (fkColoredStrandSlotEquivOfTrueCount source swapped hcount)
    (fkColoredStrandSlotEquivOfTrueCount_color source swapped hcount)

@[simp] theorem swapSplice_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    key.swapSplice.target =
      fkColoredLoopPairingPairSwapLayers key.splice.target := by
  unfold swapSplice
  apply FKColoredStrandSplice.ofColorEquiv_target

theorem swapSplice_preservesTotalC
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source) :
    key.swapSplice.PreservesTotalC := by
  unfold FKColoredStrandSplice.PreservesTotalC
  rw [← key.swapSplice.target_totalC_eq_slotPairEqualCount,
    ← fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount,
    key.swapSplice_target, fkColoredLoopPairingPairSwapLayers_totalC,
    key.splice.target_totalC key.preservesTotalC]




def SourceSeamDifferenceTwo
    {T : EvenTorus} (source : FKColoredLoopPairingPair T) : Prop :=
  (sixVertexUpCount
      (svTorusVerticalRows T (source true).arrows
        (svFinLast T.height_pos)) : Int) =
    sixVertexUpCount
      (svTorusVerticalRows T (source false).arrows
        (svFinLast T.height_pos)) + 2

theorem swapSplice_seamDelta_false
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    key.swapSplice.seamDelta false = 1 := by
  have hswap := key.swapSplice.target_upCount false
  have horiginal := key.splice.target_upCount true
  rw [key.swapSplice_target] at hswap
  change (sixVertexUpCount
      (svTorusVerticalRows T (key.splice.target true).arrows
        (svFinLast T.height_pos)) : Int) = _ at hswap
  rw [key.seamDelta_true] at horiginal
  unfold SourceSeamDifferenceTwo at hsource
  omega

theorem swapSplice_seamDelta_true
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    key.swapSplice.seamDelta true = -1 := by
  have hswap := key.swapSplice.target_upCount true
  have horiginal := key.splice.target_upCount false
  rw [key.swapSplice_target] at hswap
  change (sixVertexUpCount
      (svTorusVerticalRows T (key.splice.target false).arrows
        (svFinLast T.height_pos)) : Int) = _ at hswap
  rw [key.seamDelta_false] at horiginal
  unfold SourceSeamDifferenceTwo at hsource
  omega


noncomputable def swap
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    FKColoredFineTwoCycleUnitTransferSpliceKey source where
  splice := key.swapSplice
  preservesTotalC := key.swapSplice_preservesTotalC
  seamDelta_false := key.swapSplice_seamDelta_false hsource
  seamDelta_true := key.swapSplice_seamDelta_true hsource
  fine := by
    rw [key.swapSplice_target]
    exact (sixVertexSwapHorizontalLayers_boundedFineRowProfile
      ((key.splice.target false).arrows.horizontal,
        (key.splice.target true).arrows.horizontal)).trans key.fine
  twoCycle := by
    rw [key.swapSplice_target]
    exact sixVertexPairAtMostTwoCycleRelated_swap_target key.twoCycle

@[simp] theorem swap_target
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    (key.swap hsource).splice.target =
      fkColoredLoopPairingPairSwapLayers key.splice.target :=
  key.swapSplice_target



def paired
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source) :
    Bool → FKColoredFineTwoCycleUnitTransferSpliceKey source
  | false => key
  | true => key.swap hsource

theorem paired_target_distinct
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (key : FKColoredFineTwoCycleUnitTransferSpliceKey source)
    (hsource : SourceSeamDifferenceTwo source)
    (hlayers : key.splice.target false ≠ key.splice.target true) :
    (key.paired hsource false).splice.target ≠
      (key.paired hsource true).splice.target := by
  intro heq
  apply hlayers
  have hfalse := congrFun heq false
  simpa [paired] using hfalse

end FKColoredFineTwoCycleUnitTransferSpliceKey

end

end StatMech.FrontierD
