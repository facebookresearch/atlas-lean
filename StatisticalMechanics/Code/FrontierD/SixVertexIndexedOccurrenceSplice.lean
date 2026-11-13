/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexColoredStrandSplice












namespace StatMech.FrontierD

noncomputable section


def fkIndexedOccurrenceLayerSwap (n : Nat) : Equiv.Perm (Bool × Fin n) where
  toFun x := (!x.1, x.2)
  invFun x := (!x.1, x.2)
  left_inv x := by rcases x with ⟨layer, i⟩; cases layer <;> rfl
  right_inv x := by rcases x with ⟨layer, i⟩; cases layer <;> rfl



def fkIndexedOccurrenceSlotEmbedding
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) :
    (Bool × Fin n) ↪ FKLayeredStrandSlot T where
  toFun occurrence := (occurrence.1, key occurrence.1 occurrence.2)
  inj' := by
    rintro ⟨firstLayer, firstIndex⟩ ⟨secondLayer, secondIndex⟩ h
    have hlayer : firstLayer = secondLayer :=
      congrArg (fun slot : FKLayeredStrandSlot T => slot.1) h
    subst secondLayer
    have hindex : firstIndex = secondIndex := hinjective firstLayer
      (congrArg (fun slot : FKLayeredStrandSlot T => slot.2) h)
    rw [hindex]



noncomputable def fkIndexedOccurrenceSlotEquiv
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) :
    FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T :=
  (fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding
    (fkIndexedOccurrenceSlotEmbedding n key hinjective)

@[simp] theorem fkIndexedOccurrenceSlotEquiv_apply_key
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (layer : Bool) (i : Fin n) :
    fkIndexedOccurrenceSlotEquiv n key hinjective (layer, key layer i) =
      (!layer, key (!layer) i) := by
  change fkIndexedOccurrenceSlotEquiv n key hinjective
      (fkIndexedOccurrenceSlotEmbedding n key hinjective (layer, i)) =
    fkIndexedOccurrenceSlotEmbedding n key hinjective (!layer, i)
  exact Equiv.Perm.viaFintypeEmbedding_apply_image _ _ _

theorem fkIndexedOccurrenceSlotEquiv_apply_of_not_routed
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (slot : FKLayeredStrandSlot T)
    (hslot : ¬ exists i : Fin n, key slot.1 i = slot.2) :
    fkIndexedOccurrenceSlotEquiv n key hinjective slot = slot := by
  apply Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  rintro ⟨⟨layer, i⟩, h⟩
  have hlayer : layer = slot.1 := congrArg Prod.fst h
  subst layer
  exact hslot ⟨i, congrArg Prod.snd h⟩

@[simp] theorem fkIndexedOccurrenceSlotEquiv_apply_self
    {T : EvenTorus} (n : Nat)
    (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (slot : FKLayeredStrandSlot T) :
    fkIndexedOccurrenceSlotEquiv n key hinjective
        (fkIndexedOccurrenceSlotEquiv n key hinjective slot) = slot := by
  let embedding := fkIndexedOccurrenceSlotEmbedding n key hinjective
  by_cases hslot : slot ∈ Set.range embedding
  · obtain ⟨⟨layer, i⟩, rfl⟩ := hslot
    change ((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
        (((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
          (embedding (layer, i))) = embedding (layer, i)
    rw [Equiv.Perm.viaFintypeEmbedding_apply_image,
      Equiv.Perm.viaFintypeEmbedding_apply_image]
    cases layer <;> rfl
  · change ((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
        (((fkIndexedOccurrenceLayerSwap n).viaFintypeEmbedding embedding)
          slot) = slot
    have hfix := Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
      (fkIndexedOccurrenceLayerSwap n) embedding hslot
    rw [hfix, hfix]




def FKColoredIndexedOccurrenceBoundaryIntertwining
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer)) : Prop :=
  forall x : FKLayeredMedialDart T,
    fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective)
        (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) =
      fkColoredStrandSpliceRawColor source targetPairing
        (fkIndexedOccurrenceSlotEquiv n key hinjective) x



def FKColoredStrandSplice.ofIndexedOccurrences
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    FKColoredStrandSplice source :=
  FKColoredStrandSplice.ofBoundaryInvariant source targetPairing
    (fkIndexedOccurrenceSlotEquiv n key hinjective) hboundary

@[simp] theorem FKColoredStrandSplice.ofIndexedOccurrences_slotEquiv
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      n key hinjective hboundary).slotEquiv =
        fkIndexedOccurrenceSlotEquiv n key hinjective := rfl



theorem FKColoredStrandSplice.ofIndexedOccurrences_recover
    {T : EvenTorus} (source : FKColoredLoopPairingPair T)
    (targetPairing : Bool -> FKMedialLoopPairing T)
    (n : Nat) (key : Bool -> Fin n -> T.Vertex × Bool)
    (hinjective : forall layer, Function.Injective (key layer))
    (hboundary : FKColoredIndexedOccurrenceBoundaryIntertwining
      source targetPairing n key hinjective) :
    (FKColoredStrandSplice.ofIndexedOccurrences source targetPairing
      n key hinjective hboundary).symm.target = source :=
  FKColoredStrandSplice.symm_target _



theorem FKColoredStrandSplice.target_bigrade
    {T : EvenTorus} {source : FKColoredLoopPairingPair T}
    (splice : FKColoredStrandSplice source)
    (hC : splice.PreservesTotalC) :
    (fkColoredLoopPairingPairTotalC splice.target,
        fkColoredTrueStrandSlotCount splice.target) =
      (fkColoredLoopPairingPairTotalC source,
        fkColoredTrueStrandSlotCount source) := by
  apply Prod.ext
  · exact splice.target_totalC hC
  · exact splice.target_trueStrandSlotCount

end

end StatMech.FrontierD
