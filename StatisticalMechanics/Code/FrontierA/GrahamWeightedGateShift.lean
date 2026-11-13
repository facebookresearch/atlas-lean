/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamWeightedEq22Refinement










open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem currentConnected_add_of_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {u v : V}
    (h : CurrentConnected G (ofEdgeFun G p) u v) :
    CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) u v := by
  apply SimpleGraph.Reachable.mono (G := currentSubgraph G (ofEdgeFun G p))
    (G' := currentSubgraph G (ofEdgeFun G (fun e => p e + q e)))
  · intro x y hxy
    rcases hxy with ⟨hadj, hflux⟩
    refine ⟨hadj, ?_⟩
    have he : s(x, y) ∈ G.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact hadj
    unfold ofEdgeFun at hflux ⊢
    simp only [he, dite_true] at hflux ⊢
    omega
  · exact h



theorem sourcePairDisconnSum_gate_shift_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (B : Finset V)
    {u v m : V} (huv : u ≠ v) :
    sourcePairDisconnSum G beta J {u, v} B u m =
      sourcePairDisconnSum G beta J {u, v} B v m := by
  change gatedSourcePairSum G beta J {u, v} B
      (fun n => ¬ CurrentConnected G n u m) =
    gatedSourcePairSum G beta J {u, v} B
      (fun n => ¬ CurrentConnected G n v m)
  apply gatedSourcePairSum_congr_sources
  intro p q hp _
  have huvP : CurrentConnected G (ofEdgeFun G p) u v :=
    currentConnected_of_sources_pair G p huv hp
  have huvT : CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) u v :=
    currentConnected_add_of_left G p q huvP
  constructor
  · intro hum hvm
    exact hum (CurrentConnected.trans G huvT hvm)
  · intro hvm hum
    exact hvm (CurrentConnected.trans G (CurrentConnected.symm G huvT) hum)

end StatMech.FrontierA
