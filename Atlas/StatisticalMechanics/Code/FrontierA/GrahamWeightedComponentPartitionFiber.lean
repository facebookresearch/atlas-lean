/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.GrahamWeightedComponentPartitionCore

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem grahamComponentPairMass_eq_gatedDisconnection
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {g k l : V} (hkl : k ≠ l) (S : Finset V)
    (hS : S ∈ grahamAdmissibleComponentComplements g k l) :
    grahamComponentPairMass G beta J S g {k, l} =
      gatedSourcePairSum G beta J {k, l} ∅
        (fun n => notConnComp G n g = S ∧
          ¬ CurrentConnected G n g k) := by
  rw [grahamComponentPairMass_eq_gatedSourcePairSum]
  apply gatedSourcePairSum_congr_sources
  intro p q hp hq
  have hadm := graham_notConnComp_admissible_iff G p q (g := g) hkl hp hq
  constructor
  · intro heq
    have hm : notConnComp G (ofEdgeFun G (fun e => p e + q e)) g ∈
        grahamAdmissibleComponentComplements g k l := by simpa [heq] using hS
    exact ⟨heq, hadm.mp hm⟩
  · exact And.left



theorem grahamGatedDisconnection_eq_zero_of_not_admissible
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {g k l : V} (hkl : k ≠ l) (S : Finset V)
    (hS : S ∉ grahamAdmissibleComponentComplements g k l) :
    gatedSourcePairSum G beta J {k, l} ∅
        (fun n => notConnComp G n g = S ∧
          ¬ CurrentConnected G n g k) = 0 := by
  rw [gatedSourcePairSum_congr_sources G beta J {k, l} ∅
    (fun n => notConnComp G n g = S ∧ ¬ CurrentConnected G n g k)
    (fun _ => False)]
  · unfold gatedSourcePairSum
    simp
  · intro p q hp hq
    have hadm := graham_notConnComp_admissible_iff G p q (g := g) hkl hp hq
    constructor
    · rintro ⟨heq, hd⟩
      apply hS
      have hm := hadm.mpr hd
      simpa [heq] using hm
    · exact False.elim

end StatMech.FrontierA
