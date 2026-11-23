/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanIsCyclesCount

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanIsCyclesCount`

Applies `jic_faithfulDiscreteJordan` (the discrete Jordan count for subgraphs of `ℤ²` that are
disjoint unions of cycles) to the unit square `(0,0) - (1,0) - (1,1) - (0,1)`. Its hypothesis
`IsCycles` (every non-isolated vertex has exactly two neighbours) is proved directly by `decide`,
and the conclusion gives exactly `nullity = 1` bounded face.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanIsCyclesCount

open _root_.StatMech _root_.StatMech.Lattice _root_.SimpleGraph

/-- The 4-cycle `0 - 1 - 2 - 3 - 0`. -/
abbrev cyc4 : SimpleGraph (Fin 4) where
  Adj i j := ((j = i + 1) || (i = j + 1)) = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

/-- The unit square of `ℤ²` as a planar subgraph. -/
def unitSquare : PlanarZ2Subgraph where
  V := Fin 4
  finV := inferInstance
  decV := inferInstance
  G := cyc4
  emb := ⟨![![0, 0], ![1, 0], ![1, 1], ![0, 1]], by decide +kernel⟩
  isSub := by
    intro i j h
    change ((j = i + 1) || (i = j + 1)) = true at h
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    revert h; fin_cases i <;> fin_cases j <;> simp

-- The hypothesis `IsCycles`: every vertex of the 4-cycle has exactly two neighbours.
theorem cyc4_isCycles : cyc4.IsCycles := by
  intro v hv
  clear hv
  rw [Set.ncard_eq_toFinset_card']
  revert v; decide

theorem nullity_cyc4 : nullity cyc4 = 1 := by
  have hc : cyc4.Connected := by
    have a : ∀ i : Fin 4, cyc4.Adj i (i + 1) := by decide
    refine (connected_iff_exists_forall_reachable _).mpr ⟨0, fun i => ?_⟩
    fin_cases i
    exacts [Reachable.refl _, (a 0).reachable, (a 0).reachable.trans (a 1).reachable,
      (a 3).symm.reachable]
  have := hc.preconnected.subsingleton_connectedComponent
  have hcc : Nat.card cyc4.ConnectedComponent = 1 :=
    Nat.card_of_subsingleton (cyc4.connectedComponentMk 0)
  have he : cyc4.edgeSet.ncard = 4 := by rw [Set.ncard_eq_toFinset_card']; decide
  unfold nullity
  rw [he, hcc]
  simp

-- `jic_faithfulDiscreteJordan`: the unit square has exactly one bounded face.
example : Nat.card {c : (whb_faceRegion (imageGraph unitSquare)).ConnectedComponent //
    c.supp.Finite} = 1 := by
  obtain ⟨e⟩ := jic_faithfulDiscreteJordan unitSquare cyc4_isCycles
  rw [Nat.card_congr e]
  change Nat.card (Fin (nullity cyc4)) = 1
  rw [nullity_cyc4, Nat.card_eq_fintype_card, Fintype.card_fin]

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.JordanIsCyclesCount
