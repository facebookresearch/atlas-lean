/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexMarkedPairCTypeHall
import Code.FrontierD.FKMedialLoopVerticalWinding












open Finset Matrix Polynomial

namespace StatMech.FrontierD

noncomputable section

local instance instDecidablePropLoopFiber (p : Prop) : Decidable p :=
  Classical.propDecidable p


abbrev SixVertexCompatibleLoopPairing
    {T : EvenTorus} (omega : SixVertexArrows T) :=
  {pairing : FKMedialLoopPairing T //
    forall v, fkLoopPairingCompatible (pairing v) omega v}



def sixVertexCompatibleLoopPairingEquivPi
    {T : EvenTorus} (omega : SixVertexArrows T) :
    SixVertexCompatibleLoopPairing omega ≃
      ((v : T.Vertex) ->
        {pairing : Bool // fkLoopPairingCompatible pairing omega v}) where
  toFun pairing v := ⟨pairing.1 v, pairing.2 v⟩
  invFun choices := ⟨fun v => (choices v).1, fun v => (choices v).2⟩
  left_inv pairing := by
    apply Subtype.ext
    rfl
  right_inv choices := by
    funext v
    apply Subtype.ext
    rfl



theorem card_localCompatibleLoopPairing
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule)
    (v : T.Vertex) :
    Fintype.card
        {pairing : Bool // fkLoopPairingCompatible pairing omega v} =
      if omega.IsCType v then 2 else 1 := by
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w
  generalize he : omega.horizontal v = e
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s
  generalize hn : omega.vertical v = n
  have hice := homega v
  cases w <;> cases e <;> cases s <;> cases n <;>
    simp [Fintype.card_subtype, fkLoopPairingCompatible,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, SixVertexArrows.IsCType,
      SixVertexArrows.incomingCount, hw, he, hs, hn] at hice ⊢



theorem card_sixVertexCompatibleLoopPairing
    {T : EvenTorus} (omega : SixVertexArrows T) (homega : omega.IceRule) :
    Fintype.card (SixVertexCompatibleLoopPairing omega) =
      2 ^ sixVertexTorusCTypeCount omega := by
  rw [Fintype.card_congr (sixVertexCompatibleLoopPairingEquivPi omega),
    Fintype.card_pi]
  simp_rw [card_localCompatibleLoopPairing omega homega]
  simp_rw [show forall v : T.Vertex,
      (if omega.IsCType v then 2 else 1) =
        2 ^ (if omega.IsCType v then 1 else 0) by
    intro v
    by_cases h : omega.IsCType v <;> simp [h]]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl




noncomputable def sixVertexZeroDecorationEquivLoopPairings
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right) :
    Fin (sixVertexMarkedPairMultiplicityNat pair.1.1 pair.2.1 0) ≃
      (SixVertexCompatibleLoopPairing pair.1.1 ×
        SixVertexCompatibleLoopPairing pair.2.1) := by
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, Fintype.card_prod,
    card_sixVertexCompatibleLoopPairing pair.1.1 pair.1.2.1,
    card_sixVertexCompatibleLoopPairing pair.2.1 pair.2.2.1]
  simp [sixVertexMarkedPairMultiplicityNat, pow_add]



abbrev SixVertexLoopDecoratedPair
    (T : EvenTorus) (left right : Fin (T.width + 1)) :=
  Sigma fun pair : SixVertexMarkedSectorConfiguration T left ×
      SixVertexMarkedSectorConfiguration T right =>
    SixVertexCompatibleLoopPairing pair.1.1 ×
      SixVertexCompatibleLoopPairing pair.2.1



def sixVertexLoopDecoratedPairTotalC
    {T : EvenTorus} {left right : Fin (T.width + 1)}
    (decorated : SixVertexLoopDecoratedPair T left right) : Nat :=
  sixVertexConfigurationPairTotalC decorated.1



noncomputable def sixVertexMarkedDecoratedPairZeroEquivLoop
    (T : EvenTorus) (left right : Fin (T.width + 1)) :
    SixVertexMarkedDecoratedPair T left right 0 ≃
      SixVertexLoopDecoratedPair T left right where
  toFun decorated :=
    ⟨decorated.1,
      sixVertexZeroDecorationEquivLoopPairings decorated.1 decorated.2⟩
  invFun decorated :=
    ⟨decorated.1,
      (sixVertexZeroDecorationEquivLoopPairings decorated.1).symm
        decorated.2⟩
  left_inv decorated := by
    apply Sigma.ext
    · rfl
    · simp
  right_inv decorated := by
    apply Sigma.ext
    · rfl
    · simp

@[simp] theorem sixVertexMarkedDecoratedPairZeroEquivLoop_totalC
    (T : EvenTorus) (left right : Fin (T.width + 1))
    (decorated : SixVertexMarkedDecoratedPair T left right 0) :
    sixVertexLoopDecoratedPairTotalC
        (sixVertexMarkedDecoratedPairZeroEquivLoop T left right decorated) =
      sixVertexMarkedDecoratedPairTotalC decorated :=
  rfl




def SixVertexLoopDecoratedPairTotalCReconnection
    (T : EvenTorus) (lower middle upper : Fin (T.width + 1)) : Prop :=
  exists matching : SixVertexLoopDecoratedPair T lower upper ->
      SixVertexLoopDecoratedPair T middle middle,
    Function.Injective matching /\
      forall source,
        sixVertexLoopDecoratedPairTotalC source =
          sixVertexLoopDecoratedPairTotalC (matching source)



theorem exists_injective_decoratedZero_of_loopReconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection
      T lower middle upper) :
    exists matching : SixVertexMarkedDecoratedPair T lower upper 0 ->
        SixVertexMarkedDecoratedPair T middle middle 0,
      Function.Injective matching /\
        forall source,
          sixVertexMarkedDecoratedPairTotalC source =
            sixVertexMarkedDecoratedPairTotalC (matching source) := by
  obtain ⟨loopMatching, hinjective, htotal⟩ := hreconnect
  let sourceEquiv :=
    sixVertexMarkedDecoratedPairZeroEquivLoop T lower upper
  let targetEquiv :=
    sixVertexMarkedDecoratedPairZeroEquivLoop T middle middle
  let matching : SixVertexMarkedDecoratedPair T lower upper 0 ->
      SixVertexMarkedDecoratedPair T middle middle 0 :=
    fun source => targetEquiv.symm (loopMatching (sourceEquiv source))
  refine ⟨matching, ?_, ?_⟩
  · exact targetEquiv.symm.injective.comp
      (hinjective.comp sourceEquiv.injective)
  · intro source
    have h := htotal (sourceEquiv source)
    change sixVertexMarkedDecoratedPairTotalC source =
      sixVertexMarkedDecoratedPairTotalC
        (targetEquiv.symm (loopMatching (sourceEquiv source)))
    rw [← sixVertexMarkedDecoratedPairZeroEquivLoop_totalC
      T lower upper source,
      ← sixVertexMarkedDecoratedPairZeroEquivLoop_totalC
        T middle middle
        (targetEquiv.symm (loopMatching (sourceEquiv source)))]
    simpa [targetEquiv] using h



theorem configurationPairTotalCFiberDominates_of_loopReconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection
      T lower middle upper) :
    SixVertexConfigurationPairTotalCFiberDominates
      T lower middle upper := by
  have hdecorated :
      SixVertexMarkedDecoratedPairTotalCFiberDominates
        T lower middle upper 0 :=
    (exists_injective_gradePreserving_iff_fiberCard
      (fun source : SixVertexMarkedDecoratedPair T lower upper 0 =>
        sixVertexMarkedDecoratedPairTotalC source)
      (fun target : SixVertexMarkedDecoratedPair T middle middle 0 =>
        sixVertexMarkedDecoratedPairTotalC target)).mp
      (exists_injective_decoratedZero_of_loopReconnection hreconnect)
  intro total
  have htotal := hdecorated total
  rw [card_sixVertexMarkedDecoratedPairTotalCFiber,
    card_sixVertexMarkedDecoratedPairTotalCFiber] at htotal
  simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one] at htotal
  exact Nat.le_of_mul_le_mul_right htotal (pow_pos (by norm_num) total)



theorem configurationPairTotalCReconnection_of_loopReconnection
    {T : EvenTorus} {lower middle upper : Fin (T.width + 1)}
    (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection
      T lower middle upper) :
    SixVertexConfigurationPairTotalCReconnection T lower middle upper :=
  (configurationPairTotalCReconnection_iff_fiberDominates
    T lower middle upper).mpr
      (configurationPairTotalCFiberDominates_of_loopReconnection hreconnect)



def SixVertexCompatibleLoopPairing.toOrientedMedialLoops
    {T : EvenTorus} {omega : SixVertexArrows T}
    (pairing : SixVertexCompatibleLoopPairing omega) :
    FKOrientedMedialLoops T where
  pairing := pairing.1
  arrows := omega
  compatible := pairing.2

end

end StatMech.FrontierD
