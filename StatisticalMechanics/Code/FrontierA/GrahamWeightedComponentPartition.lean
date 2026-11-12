/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.GrahamWeightedComponentPartitionFiber

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem grahamDisconnectedPairMass_eq_sourcePairDisconnSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {g k l : V} (hkl : k ≠ l) :
    grahamDisconnectedPairMass G beta J g k l =
      sourcePairDisconnSum G beta J {k, l} ∅ g k := by
  let P : Current V -> Prop := fun n =>
    ¬ CurrentConnected G n g k
  let f : Current V -> Finset V := fun n => notConnComp G n g
  have hpart := gatedSourcePairSum_partition G beta J {k, l} ∅ P f
  have hdisc : sourcePairDisconnSum G beta J {k, l} ∅ g k =
      gatedSourcePairSum G beta J {k, l} ∅ P := by rfl
  rw [hdisc, hpart]
  unfold grahamDisconnectedPairMass
  calc
    (∑ S ∈ grahamAdmissibleComponentComplements g k l,
        grahamComponentPairMass G beta J S g {k, l}) =
      ∑ S ∈ grahamAdmissibleComponentComplements g k l,
        gatedSourcePairSum G beta J {k, l} ∅
          (fun n => f n = S ∧ P n) := by
            apply Finset.sum_congr rfl
            intro S hS
            exact grahamComponentPairMass_eq_gatedDisconnection
              G beta J hkl S hS
    _ = ∑ S : Finset V, gatedSourcePairSum G beta J {k, l} ∅
          (fun n => f n = S ∧ P n) := by
            apply Finset.sum_subset (Finset.subset_univ _)
            intro S _ hS
            exact grahamGatedDisconnection_eq_zero_of_not_admissible
              G beta J hkl S hS



theorem sourcePairDisconnSum_eq_restrictedVacuumComponentMass
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {g k l : V} (hkl : k ≠ l) :
    sourcePairDisconnSum G beta J {k, l} ∅ g k =
      grahamRestrictedVacuumComponentMass G beta J g k l := by
  rw [← grahamDisconnectedPairMass_eq_sourcePairDisconnSum G beta J hkl]
  exact grahamDisconnectedPairMass_eq_restrictedVacuumComponentMass G beta J g k l



theorem graham_full_mul_vacuum_sub_sourcePairDisconn_eq_gksDrop
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {g k l : V} (hkl : k ≠ l) :
    expectationJ G beta J {k, l} *
        (∑ S ∈ grahamAdmissibleComponentComplements g k l,
          grahamComponentPairMass G beta J S g ∅) -
      sourcePairDisconnSum G beta J {k, l} ∅ g k =
    ∑ S ∈ grahamAdmissibleComponentComplements g k l,
      grahamComponentPairMass G beta J S g ∅ *
        (expectationJ G beta J {k, l} -
          expectationJ G beta (StatMech.Sharpness.couplingIn J S) {k, l}) := by
  rw [← grahamDisconnectedPairMass_eq_sourcePairDisconnSum G beta J hkl]
  exact graham_full_mul_vacuum_sub_disconnected_eq_gksDrop G beta J g k l

end StatMech.FrontierA
