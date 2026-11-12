/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexSectorTransferBridge
import Code.Foundations.ConfigSpace

open Finset Matrix

namespace StatMech.FrontierD




abbrev FKMedialConfiguration (T : EvenTorus) := ConfigSpace T.Vertex




abbrev FKMedialLoopPairing (T : EvenTorus) := T.Vertex -> Bool

def fkConfigurationToMedialPairing (T : EvenTorus) :
    FKMedialConfiguration T ≃ FKMedialLoopPairing T := Equiv.refl _

def fkLoopWestIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  omega.horizontal (SixVertexArrows.cyclicPred T.width_pos v.1, v.2)

def fkLoopEastIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  !omega.horizontal v

def fkLoopSouthIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  omega.vertical (v.1, SixVertexArrows.cyclicPred T.height_pos v.2)

def fkLoopNorthIncoming (omega : SixVertexArrows T) (v : T.Vertex) : Bool :=
  !omega.vertical v



def fkLoopPairingCompatible (pairing : Bool)
    (omega : SixVertexArrows T) (v : T.Vertex) : Prop :=
  if pairing then
    fkLoopWestIncoming omega v ≠ fkLoopSouthIncoming omega v ∧
      fkLoopEastIncoming omega v ≠ fkLoopNorthIncoming omega v
  else
    fkLoopWestIncoming omega v ≠ fkLoopNorthIncoming omega v ∧
      fkLoopEastIncoming omega v ≠ fkLoopSouthIncoming omega v

noncomputable instance fkLoopPairingCompatibleDecidable
    (pairing : Bool) (omega : SixVertexArrows T) (v : T.Vertex) :
    Decidable (fkLoopPairingCompatible pairing omega v) :=
  Classical.propDecidable _


theorem incomingCount_eq_two_of_fkLoopPairingCompatible
    (pairing : Bool) (omega : SixVertexArrows T) (v : T.Vertex)
    (h : fkLoopPairingCompatible pairing omega v) :
    omega.incomingCount v = 2 := by
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w at h ⊢
  generalize he : omega.horizontal v = e at h ⊢
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s at h ⊢
  generalize hn : omega.vertical v = n at h ⊢
  cases pairing <;> cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkLoopPairingCompatible, fkLoopWestIncoming,
      fkLoopEastIncoming, fkLoopSouthIncoming, fkLoopNorthIncoming,
      SixVertexArrows.incomingCount, hw, he, hs, hn] at h ⊢



structure FKOrientedMedialLoops (T : EvenTorus) where
  pairing : FKMedialLoopPairing T
  arrows : SixVertexArrows T
  compatible : forall v, fkLoopPairingCompatible (pairing v) arrows v



def FKOrientedMedialLoops.toSixVertexConfiguration
    (loops : FKOrientedMedialLoops T) : SixVertexConfiguration T :=
  ⟨loops.arrows, fun v =>
    incomingCount_eq_two_of_fkLoopPairingCompatible
      (loops.pairing v) loops.arrows v (loops.compatible v)⟩








noncomputable def fkOrientedLoopLocalWeight
    (lam : Real) (pairing : Bool)
    (omega : SixVertexArrows T) (v : T.Vertex) : Real := by
  classical
  exact if fkLoopPairingCompatible pairing omega v then
      if omega.IsCType v then
        if pairing = fkLoopWestIncoming omega v then
          Real.exp (lam / 2) else Real.exp (-lam / 2)
      else 1
    else 0


theorem sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight
    (lam : Real) (omega : SixVertexArrows T) (v : T.Vertex) :
    (∑ pairing : Bool,
      fkOrientedLoopLocalWeight lam pairing omega v) =
      omega.localWeight
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) v := by
  generalize hw : omega.horizontal
    (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) = w
  generalize he : omega.horizontal v = e
  generalize hs : omega.vertical
    (v.1, SixVertexArrows.cyclicPred T.height_pos v.2) = s
  generalize hn : omega.vertical v = n
  cases w <;> cases e <;> cases s <;> cases n <;>
    simp [fkOrientedLoopLocalWeight, fkLoopPairingCompatible,
      fkLoopWestIncoming, fkLoopEastIncoming, fkLoopSouthIncoming,
      fkLoopNorthIncoming, SixVertexArrows.localWeight,
      SixVertexArrows.incomingCount, SixVertexArrows.IsCType,
      hw, he, hs, hn, add_comm]


noncomputable def fkOrientedLoopPairingWeight
    (lam : Real) (pairing : FKMedialLoopPairing T)
    (omega : SixVertexArrows T) : Real :=
  ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v



noncomputable def fkOrientedLoopPartitionSum
    (T : EvenTorus) (lam : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    ∑ pairing : FKMedialLoopPairing T,
      fkOrientedLoopPairingWeight lam pairing omega




theorem fkOrientedLoopPartitionSum_eq_sixVertexTorusArrowPartitionSum
    (T : EvenTorus) (lam : Real) :
    fkOrientedLoopPartitionSum T lam =
      sixVertexTorusArrowPartitionSum T
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
  rw [fkOrientedLoopPartitionSum, sixVertexTorusArrowPartitionSum]
  apply Finset.sum_congr rfl
  intro omega homega
  change (∑ pairing : FKMedialLoopPairing T,
      ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v) =
    ∏ v, omega.localWeight
      (Real.exp (lam / 2) + Real.exp (-lam / 2)) v
  calc
    (∑ pairing : FKMedialLoopPairing T,
        ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v) =
      ∏ v, ∑ pairing : Bool,
        fkOrientedLoopLocalWeight lam pairing omega v :=
      (Fintype.prod_sum (fun v pairing =>
        fkOrientedLoopLocalWeight lam pairing omega v)).symm
    _ = ∏ v, omega.localWeight
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) v := by
      apply Finset.prod_congr rfl
      intro v hv
      exact sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight lam omega v




def FKOrientedMedialLoops.seamUpCount
    (loops : FKOrientedMedialLoops T) : Nat :=
  sixVertexUpCount
    (svTorusVerticalRows T loops.arrows (svFinLast T.height_pos))

@[simp] theorem FKOrientedMedialLoops.toSixVertexConfiguration_seamUpCount
    (loops : FKOrientedMedialLoops T) :
    sixVertexUpCount
        (svTorusVerticalRows T loops.toSixVertexConfiguration.1
          (svFinLast T.height_pos)) =
      loops.seamUpCount := rfl


noncomputable def fkOrientedLoopSectorPartitionSum
    (T : EvenTorus) (n : Fin (T.width + 1)) (lam : Real) : Real :=
  ∑ omega : SixVertexArrows T,
    if sixVertexUpCount
        (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val then
      ∑ pairing : FKMedialLoopPairing T,
        fkOrientedLoopPairingWeight lam pairing omega
    else 0




theorem fkOrientedLoopSectorPartitionSum_eq_sixVertexSector
    (T : EvenTorus) (n : Fin (T.width + 1)) (lam : Real) :
    fkOrientedLoopSectorPartitionSum T n lam =
      svTorusSectorArrowPartitionSum T n
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) := by
  rw [fkOrientedLoopSectorPartitionSum, svTorusSectorArrowPartitionSum]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hn : sixVertexUpCount
      (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n.val
  · simp only [if_pos hn]
    change (∑ pairing : FKMedialLoopPairing T,
        ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v) =
      ∏ v, omega.localWeight
        (Real.exp (lam / 2) + Real.exp (-lam / 2)) v
    calc
      (∑ pairing : FKMedialLoopPairing T,
          ∏ v, fkOrientedLoopLocalWeight lam (pairing v) omega v) =
        ∏ v, ∑ pairing : Bool,
          fkOrientedLoopLocalWeight lam pairing omega v :=
        (Fintype.prod_sum (fun v pairing =>
          fkOrientedLoopLocalWeight lam pairing omega v)).symm
      _ = ∏ v, omega.localWeight
          (Real.exp (lam / 2) + Real.exp (-lam / 2)) v := by
        apply Finset.prod_congr rfl
        intro v hv
        exact sum_fkOrientedLoopLocalWeight_eq_sixVertexLocalWeight
          lam omega v
  · simp [hn]



theorem fkOrientedLoopFixedChargePartitionSum_eq_sectorTrace
    (T : EvenTorus) (r : Nat) (_hr : r <= T.width / 2) (lam : Real) :
    fkOrientedLoopSectorPartitionSum T
        ⟨T.width / 2 - r, Nat.lt_succ_of_le
          ((Nat.sub_le _ _).trans (Nat.div_le_self T.width 2))⟩ lam =
      Matrix.trace
        (sixVertexSectorTransfer T.width (T.width / 2 - r)
          (Real.exp (lam / 2) + Real.exp (-lam / 2)) ^ T.height) := by
  rw [fkOrientedLoopSectorPartitionSum_eq_sixVertexSector]
  exact svTorusSectorArrowPartitionSum_eq_sectorTrace T _ _

end StatMech.FrontierD
