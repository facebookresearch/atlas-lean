/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierA.GrahamWeightedNormalization
import Code.Sharpness.GhostCurrentRep

open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

namespace StatMech.FrontierA

open StatMech.Sharpness
open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]



theorem sourcePairDisconnSum_comm
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (A B : Finset V) (u v : V) :
    sourcePairDisconnSum G beta J A B u v =
      sourcePairDisconnSum G beta J A B v u := by
  unfold sourcePairDisconnSum
  apply tsum_congr
  rintro ⟨p, q⟩
  let n := ofEdgeFun G (fun e => p e + q e)
  have hiff : CurrentConnected G n u v ↔ CurrentConnected G n v u :=
    ⟨CurrentConnected.symm G, CurrentConnected.symm G⟩
  by_cases h : CurrentConnected G n u v
  · have hvu := hiff.mp h
    simp [n, h, hvu]
  · have hnvu : ¬ CurrentConnected G n v u := fun hvu => h (hiff.mpr hvu)
    simp [n, h, hnvu]



theorem pairSources_symmDiff_bridge
    {i k m : V} (hik : i ≠ k) (him : i ≠ m) (hkm : k ≠ m) :
    ({i, k} : Finset V) ∆ {i, m} = {k, m} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hxi : x = i <;> by_cases hxk : x = k <;>
    by_cases hxm : x = m <;> simp_all [eq_comm]



theorem expectationBridgeGap_eq_sourcePairDisconn
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i k m : V} (hik : i ≠ k) (him : i ≠ m) (hkm : k ≠ m) :
    expectationJ G beta J {i, k} -
        expectationJ G beta J {i, m} * expectationJ G beta J {m, k} =
      sourcePairDisconnSum G beta J {i, k} ∅ i m /
        currentSum G beta J ∅ ^ 2 := by
  have hcur := StatMech.Sharpness.GhostCurrentRep.gcr_currentSum_ghostRep
    G beta J ({i, k} : Finset V) him
  rw [pairSources_symmDiff_bridge hik him hkm] at hcur
  have hmk : currentSum G beta J {m, k} = currentSum G beta J {k, m} := by
    congr 1
    ext x
    simp [or_comm]
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta J)
  rw [current_representation, current_representation, current_representation]
  rw [hmk]
  field_simp [hZ]
  ring_nf at hcur ⊢
  exact hcur



theorem auxiliaryConnectionMass_div_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real)
    {i j m : V} (hij : i ≠ j) (him : i ≠ m) (hjm : j ≠ m) :
    StatMech.Walls.gc37_sourcePairConnSum G beta J {i, j} ∅ i m /
        currentSum G beta J ∅ ^ 2 =
      expectationJ G beta J {i, m} * expectationJ G beta J {j, m} := by
  rw [grahamAuxConnectionMass_eq_currentSums G beta J hij him hjm]
  rw [current_representation, current_representation]
  have hZ : currentSum G beta J ∅ ≠ 0 :=
    ne_of_gt (StatMech.Ising.acr_currentSum_empty_pos G beta J)
  field_simp [hZ]

end StatMech.FrontierA
