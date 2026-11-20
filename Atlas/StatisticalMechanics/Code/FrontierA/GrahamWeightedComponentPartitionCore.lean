/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.GrahamWeightedComponentResummation
import Code.Sharpness.DeltaBound

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option maxHeartbeats 8000000

namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]




theorem graham_notConnComp_admissible_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : ↥G.edgeFinset -> Nat) {g k l : V} (hkl : k ≠ l)
    (hp : sources G (ofEdgeFun G p) = {k, l})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    notConnComp G (ofEdgeFun G (fun e => p e + q e)) g ∈
        grahamAdmissibleComponentComplements g k l ↔
      ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) g k := by
  let n : Current V := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G n = {k, l} := by
    dsimp [n]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext x
    simp [Finset.mem_symmDiff]
  have hklC : CurrentConnected G n k l :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hkl hsrc
  rw [grahamAdmissibleComponentComplements, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨_, hk, _⟩
    rw [mem_notConnComp] at hk
    exact hk
  · intro hdisc
    have hg : g ∉ notConnComp G n g := by
      rw [mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G n g)
    have hk : k ∈ notConnComp G n g := by
      rw [mem_notConnComp]
      exact hdisc
    have hl : l ∈ notConnComp G n g := by
      rw [mem_notConnComp]
      intro hgl
      exact hdisc (CurrentConnected.trans G hgl (CurrentConnected.symm G hklC))
    exact ⟨hg, hk, hl⟩

end StatMech.FrontierA
