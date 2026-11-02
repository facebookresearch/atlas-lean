/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Backbone.ExplorationSelectorAdmissible

/-!
# Active segment fibers

The unconditional remainder of the current dynamic selector development: the weight of an
active segment fiber is the segment numerator.

The vacuous selector API was removed: `shb_CurrentDynamicSelector` is empty whenever `V` has
two distinct vertices, so `actualFiberRealizes`, `actualMass_eq_generated`, the switching law,
and the downstream bondwise reindexing route quantified over it established no switching
result. The unconditional active-segment fiber identity below is retained.

## i. Overview

`shb_ActiveSegmentFiber` is the set of currents on a domain whose sources are the endpoints of
an active segment and whose selected backbone is that segment. Its weight mass is the segment
numerator (`shb_activeSegmentFiberMass_eq_segmentNum`).

## ii. Key results

- `shb_activeSegmentFiberMass_eq_segmentNum` : the weight mass of an active segment fiber is
  the segment numerator

## iii. Table of contents

- A. Active segment fibers

## iv. References

- H. Duminil-Copin, V. Tassion, "A new proof of the sharpness of the phase transition for
  Bernoulli percolation and the Ising model", Comm. Math. Phys. 343 (2016) 725–745

-/

@[expose] public section

open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-- Classical decidability of adjacency, used throughout this file. -/
local instance (H : SimpleGraph V) : DecidableRel H.Adj :=
  Classical.decRel _

/-! ## A. Active segment fibers -/

/-- The current weight of an edge function on the domain graph. -/
noncomputable def shb_explorationCoordinateWeight
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) : Real :=
  weight d.graph beta J (ofEdgeFun d.graph m)

/-- The currents on the domain graph with sources the endpoints of an active segment whose
selected backbone is that segment. -/
def shb_ActiveSegmentFiber
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) (m : d.graph.edgeFinset -> Nat) : Prop :=
  sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} /\
    shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
      some (s.toPath d.graph (d.active_supported s hs))

/-- Classical decidability of active segment fibers. -/
noncomputable instance shb_ActiveSegmentFiber_decidable
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) : DecidablePred (shb_ActiveSegmentFiber d s hs) :=
  Classical.decPred _

lemma shb_summable_explorationFiberIndicator
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V)
    (P : (d.graph.edgeFinset -> Nat) -> Prop) [DecidablePred P] :
    Summable (fun m => if P m then
      shb_explorationCoordinateWeight beta J d m else 0) := by
  let f := fun m : d.graph.edgeFinset -> Nat =>
    shb_explorationCoordinateWeight beta J d m
  have hf : Summable f := shb_summable_weight d.graph beta J
  have heq : (fun m => if P m then f m else 0) =
      Set.indicator {m | P m} f := by
    funext m
    by_cases hm : P m <;> simp [Set.indicator, hm]
  rw [heq]
  exact hf.indicator _

/-- The weight mass of an active segment fiber is the segment numerator. -/
lemma shb_activeSegmentFiberMass_eq_segmentNum
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (hs : s ∈ d.active) :
    (∑' m : d.graph.edgeFinset -> Nat,
      if shb_ActiveSegmentFiber d s hs m then
        shb_explorationCoordinateWeight beta J d m else 0) =
      shb_segmentNum beta J d s := by
  unfold shb_segmentNum
  rw [dite_eq_left hs]
  unfold shb_backboneNumSupport shb_ActiveSegmentFiber
    shb_explorationCoordinateWeight
  apply tsum_congr
  intro m
  by_cases h :
      sources d.graph (ofEdgeFun d.graph m) = {s.1, s.2.1} /\
        shb_backboneSelectSupport d.graph (ofEdgeFun d.graph m) s.1 s.2.1 =
          some (s.toPath d.graph (d.active_supported s hs)) <;> simp [h]

end

end StatMech.Sharpness
