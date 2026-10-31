/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanExteriorClosure
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.OrbitWindingWitness
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.WindingWitness
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.MinimalPeriodLoop
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BdEdgeMatchFinite
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.RayCrossFlip
public import PhyslibExt.CondensedMatter.IsingModel.KramersWannier.BridgeGap

/-!
# Reformulations of the crossing-edge matching for closed walks

Equivalent forms of `rpc_CrossEdgeOddIffOnWalk` for a closed lattice walk, in terms of edge
membership, boundary edges of the inside region, and the two inclusions between them.

## i. Overview

For a walk without repeated edges, an edge is traversed an odd number of times iff it is an edge of
the walk. So `rpc_CrossEdgeOddIffOnWalk Vc` says that `rpc_crossEdge u v` is an edge of `Vc` iff
`uv` is, and, by `rpc_crossFlip`, that the boundary edges of the inside region of `Vc` are exactly
the edges of `Vc`. The latter splits into `jbw_hard_gap Vc` and its converse.

Headline fidelity:
- The equivalences `dow_bridge_iff_crossEdge_mem_iff_shared_mem`,
  `dow_bridge_iff_bdEdge_shared_mem` and `dow_bridge_iff_hardGap_and_reverse` are unconditional.
- `dow_primalWalkLeftRegionMatch_of_hardGap_and_reverse` is vacuous. Its hypothesis `hnd` (every
  closed walk has no repeated edges) is false: a walk that goes along an edge and back repeats it.
  Its conclusion is refuted by `StatMech.Walls.ceo_primalWalkLeftRegionMatch_false`.

## ii. Key results

- `StatMech.Walls.dow_bridge_iff_bdEdge_shared_mem` : crossing-edge matching ↔ boundary edges
  of the inside are the edges of the walk
- `StatMech.Walls.dow_bridge_iff_hardGap_and_reverse` : the same split into two inclusions
- `StatMech.Walls.dow_unitSquare_bridgeBody` : the unit-square instance at one edge

## iii. Table of contents

- A. Odd counts and membership
- B. Equivalent forms of the crossing-edge matching

## iv. References

None beyond those in the imported modules.
-/

@[expose] public section

open Set SimpleGraph
open scoped BigOperators

namespace StatMech

namespace Walls

open StatMech.Lattice

/-! ## A. Odd counts and membership -/

/-- In a list without duplicates an element occurs an odd number of times iff it occurs. -/
lemma dow_odd_count_iff_mem_of_nodup {α : Type*} [DecidableEq α] {l : List α} (hnd : l.Nodup)
    (e : α) : Odd (l.count e) ↔ e ∈ l := by
  constructor
  · intro hodd
    rcases Nat.eq_zero_or_pos (l.count e) with h0 | hpos
    · rw [h0] at hodd; exact absurd hodd (by decide)
    · exact List.count_pos_iff.mp hpos
  · intro hmem
    rw [List.count_eq_one_of_mem hnd hmem]
    exact ⟨0, rfl⟩

/-- For a walk without repeated edges, an edge is traversed an odd number of times iff it is an edge
of the walk. -/
lemma dow_walk_odd_count_iff_mem {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) (e : Sym2 (Site 2)) :
    Odd (Vc.edges.count e) ↔ e ∈ Vc.edges :=
  dow_odd_count_iff_mem_of_nodup hnd e

/-! ## B. Equivalent forms of the crossing-edge matching -/

/-- For a walk without repeated edges, `rpc_CrossEdgeOddIffOnWalk` says that `rpc_crossEdge u v` is
an edge of the walk iff `uv` is. -/
lemma dow_bridge_iff_crossEdge_mem_iff_shared_mem {a : Site 2}
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

/-- `rpc_CrossEdgeOddIffOnWalk Vc` iff the boundary edges of the inside region of `Vc` are exactly
the edges of `Vc`. -/
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

/-- `rpc_CrossEdgeOddIffOnWalk Vc` iff `jbw_hard_gap Vc` and every boundary edge of the inside is an
edge of `Vc`. -/
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

/-- The two inclusions give `rpc_CrossEdgeOddIffOnWalk Vc`. -/
lemma dow_bridge_of_hardGap_and_reverse {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) (hhard : jbw_hard_gap Vc)
    (hrev : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v →
      bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) :
    rpc_CrossEdgeOddIffOnWalk Vc :=
  (dow_bridge_iff_hardGap_and_reverse Vc hnd).mpr ⟨hhard, hrev⟩

/-- Assembling the two inclusions for all closed walks gives `kwc_PrimalWalkLeftRegionMatch`.
Vacuous: the hypothesis `hnd` (no closed walk repeats an edge) is false, and the conclusion is
refuted by `ceo_primalWalkLeftRegionMatch_false`. -/
lemma dow_primalWalkLeftRegionMatch_of_hardGap_and_reverse
    (hnd : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup)
    (hhard : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), jbw_hard_gap Vc)
    (hrev : ∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {u v : Site 2},
      (hypercubicLattice 2).Adj u v →
      bdEdge (jec_leftRegion Vc) s(u, v) → s(u, v) ∈ Vc.edges) :
    kwc_PrimalWalkLeftRegionMatch :=
  rpc_primalWalkLeftRegionMatch_of_bridge (fun Vc =>
    dow_bridge_of_hardGap_and_reverse Vc (hnd Vc) (hhard Vc) (fun hadj => hrev Vc hadj))

/-- For the unit-square loop and the edge `(0, 1)`–`(1, 1)`, odd crossing-edge count and
boundary-edge membership agree. -/
lemma dow_unitSquare_bridgeBody :
    Odd (wwit_unitSquareLoop.edges.count
      (rpc_crossEdge (![0, 1] : Site 2) (![1, 1] : Site 2))) ↔
      bdEdge (jec_leftRegion wwit_unitSquareLoop) s((![0, 1] : Site 2), (![1, 1] : Site 2)) :=
  ⟨fun _ => rpc_unitSquare_flip, fun _ => rpc_unitSquare_crossEdge_odd⟩

end Walls

end StatMech
