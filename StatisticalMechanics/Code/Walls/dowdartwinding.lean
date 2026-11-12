/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































































import Mathlib
import Code.Lattice.JordanExteriorClosure
import Code.Lattice.OrbitWindingWitness
import Code.Lattice.WindingWitness
import Code.Lattice.MinimalPeriodLoop
import Code.Lattice.BdEdgeMatchClose
import Code.Walls.rpccrossflip
import Code.Walls.jbwbridge

open Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem dow_odd_count_iff_mem_of_nodup {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    (e : α) : Odd (l.count e) ↔ e ∈ l := by
  constructor
  · intro hodd
    
    rcases Nat.eq_zero_or_pos (l.count e) with h0 | hpos
    · rw [h0] at hodd; exact absurd hodd (by decide)
    · exact List.count_pos_iff.mp hpos
  · intro hmem
    rw [List.count_eq_one_of_mem hnd hmem]
    exact ⟨0, rfl⟩





theorem dow_walk_odd_count_iff_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) (e : Sym2 (Site 2)) :
    Odd (Vc.edges.count e) ↔ e ∈ Vc.edges :=
  dow_odd_count_iff_mem_of_nodup hnd e



















theorem dow_bridge_iff_crossEdge_mem_iff_shared_mem {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) (hnd : Vc.edges.Nodup) :
    rpc_CrossEdgeOddIffOnWalk Vc ↔
      (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (rpc_crossEdge u v ∈ Vc.edges ↔ s(u, v) ∈ Vc.edges)) := by
  constructor
  · intro hbridge u v hadj
    have := hbridge hadj
    rwa [dow_walk_odd_count_iff_mem Vc hnd (rpc_crossEdge u v)] at this
  · intro hmem u v hadj
    rw [dow_walk_odd_count_iff_mem Vc hnd (rpc_crossEdge u v)]
    exact hmem hadj

















theorem dow_bridge_iff_bdEdge_shared_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) :
    rpc_CrossEdgeOddIffOnWalk Vc ↔
      (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
        (bdEdge (jec_leftRegion Vc) s(u, v) ↔ s(u, v) ∈ Vc.edges)) := by
  constructor
  · intro hbridge u v hadj
    rw [rpc_crossFlip Vc hadj]
    exact hbridge hadj
  · intro hmatch u v hadj
    rw [← rpc_crossFlip Vc hadj]
    exact hmatch hadj















theorem dow_bdEdge_meets_support {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
    u ∈ Vc.support ∨ v ∈ Vc.support :=
  bemc_bdEdge_imp_on_support Vc hadj hbd






theorem dow_off_support_not_bdEdge {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    ¬ bdEdge (jec_leftRegion Vc) s(u, v) :=
  bemc_off_support_not_bdEdge Vc hadj hu hv
























theorem dow_bridge_iff_hardGap_and_reverse {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (_hnd : Vc.edges.Nodup) :
    rpc_CrossEdgeOddIffOnWalk Vc ↔
      (jbw_hard_gap Vc ∧
        ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
          bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) := by
  rw [dow_bridge_iff_bdEdge_shared_mem Vc]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro u v hadj he
      rw [List.mem_toFinset] at he
      exact (h hadj).mpr he
    · intro u v hadj hbd
      exact (h hadj).mp hbd
  · rintro ⟨hhard, hrev⟩ u v hadj
    exact ⟨fun hbd => hrev hadj hbd, fun he => hhard hadj (List.mem_toFinset.mpr he)⟩
































theorem dow_bridge_of_hardGap_and_reverse {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) (hhard : jbw_hard_gap Vc)
    (hrev : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) :
    rpc_CrossEdgeOddIffOnWalk Vc :=
  (dow_bridge_iff_hardGap_and_reverse Vc hnd).mpr ⟨hhard, hrev⟩






theorem dow_primalWalkLeftRegionMatch_of_hardGap_and_reverse
    (hnd : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup)
    (hhard : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc)
    (hrev : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2},
      (hypercubicLattice 2).Adj u v →
      bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) :
    kwc_PrimalWalkLeftRegionMatch :=
  rpc_primalWalkLeftRegionMatch_of_bridge (fun Vc =>
    dow_bridge_of_hardGap_and_reverse Vc (hnd Vc) (hhard Vc) (fun hadj => hrev Vc hadj))
















theorem dow_unitSquare_bridgeBody :
    Odd (wwit_unitSquareLoop.edges.count
      (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) ↔
      bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) :=
  ⟨fun _ => rpc_unitSquare_flip, fun _ => rpc_unitSquare_crossEdge_odd⟩

end Walls

end StatMech
