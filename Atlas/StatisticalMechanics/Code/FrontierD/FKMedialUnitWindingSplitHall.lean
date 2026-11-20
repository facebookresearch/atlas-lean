/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialToggleExact
import Code.FrontierD.PermSameCycleWeightSplit
import Code.FrontierD.SixVertexUnitComponentHall











open Equiv Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

variable {T : EvenTorus}

local instance fkMedialUnitWindingSplitHallPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p



theorem fkMedialBlackBoundaryCycleWeight_split_of_reachable
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hreach : (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    {A : Type*} [AddCommGroup A]
    (oldWeight newWeight : FKMedialBlackDart T -> A)
    (haway : forall d,
      d ≠ fkMedialBlackDart0 v -> d ≠ fkMedialBlackDart1 v ->
        oldWeight d = newWeight d)
    (hpair : oldWeight (fkMedialBlackDart0 v) +
          oldWeight (fkMedialBlackDart1 v) =
        newWeight (fkMedialBlackDart0 v) +
          newWeight (fkMedialBlackDart1 v)) :
    permCycleClassWeightSum (fkMedialBlackBoundaryPerm pairing)
          (fkMedialBlackDart0 v) oldWeight =
      permCycleClassWeightSum
          (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v))
          (fkMedialBlackDart0 v) newWeight +
        permCycleClassWeightSum
          (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v))
          (fkMedialBlackDart1 v) newWeight := by
  let sigma := fkMedialBlackBoundaryPerm pairing
  let a := fkMedialBlackDart0 v
  let b := fkMedialBlackDart1 v
  have hab : sigma.SameCycle a b := by
    apply (fkMedial_blackBoundary_sameCycle_iff_reachable pairing a b).2
    exact (fkMedialBlackDarts_reachable_iff_west_east pairing v).2 hreach
  have hcount : permCycleCount (sigma * Equiv.swap a b) =
      permCycleCount sigma + 1 := by
    change permCycleCount
        (fkMedialBlackBoundaryPerm pairing * fkMedialBlackDartSwap v) =
      permCycleCount (fkMedialBlackBoundaryPerm pairing) + 1
    rw [<- fkMedialBlackBoundaryPerm_toggle pairing v,
      permCycleCount_fkMedialBlackBoundaryPerm,
      permCycleCount_fkMedialBlackBoundaryPerm]
    exact (fkMedialLoopCount_toggle_of_reachable T pairing v hreach).symm
  have hsplit := permCycleClassWeightSum_split sigma a b
    (fkMedialBlackDart0_ne_dart1 v) hab hcount
    oldWeight newWeight haway hpair
  rw [fkMedialBlackBoundaryPerm_toggle]
  simpa only [sigma, a, b, fkMedialBlackDartSwap] using hsplit



theorem fkMedialBlackBoundaryCycleWeight_split_two_units
    (pairing : FKMedialLoopPairing T) (v : T.Vertex)
    (hreach : (fkMedialLoopGraph T pairing).Reachable
      (fkMedialWestDart v) (fkMedialEastDart v))
    (oldWeight newWeight : FKMedialBlackDart T -> Int)
    (haway : forall d,
      d ≠ fkMedialBlackDart0 v -> d ≠ fkMedialBlackDart1 v ->
        oldWeight d = newWeight d)
    (hpair : oldWeight (fkMedialBlackDart0 v) +
          oldWeight (fkMedialBlackDart1 v) =
        newWeight (fkMedialBlackDart0 v) +
          newWeight (fkMedialBlackDart1 v))
    (hold : permCycleClassWeightSum (fkMedialBlackBoundaryPerm pairing)
      (fkMedialBlackDart0 v) oldWeight = 2)
    (hfirst : 0 < permCycleClassWeightSum
      (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v))
      (fkMedialBlackDart0 v) newWeight)
    (hsecond : 0 < permCycleClassWeightSum
      (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v))
      (fkMedialBlackDart1 v) newWeight) :
    permCycleClassWeightSum
        (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v))
        (fkMedialBlackDart0 v) newWeight = 1 /\
      permCycleClassWeightSum
        (fkMedialBlackBoundaryPerm (fkMedialTogglePairingAt pairing v))
        (fkMedialBlackDart1 v) newWeight = 1 := by
  have hsplit := fkMedialBlackBoundaryCycleWeight_split_of_reachable
    pairing v hreach oldWeight newWeight haway hpair
  rw [hold] at hsplit
  constructor <;> omega




theorem booleanTwoUnitComponentDownRelation_hall :
    forall sources : Finset (BooleanLayer Bool 2),
      sources.card <=
        (Finset.univ.filter fun target : BooleanLayer Bool 1 =>
          ∃ source ∈ sources,
            booleanMiddleLayerDownRelation source target).card := by
  apply booleanMiddleLayerDownRelation_hall (Component := Bool) 1
  simp

end

end StatMech.FrontierD
