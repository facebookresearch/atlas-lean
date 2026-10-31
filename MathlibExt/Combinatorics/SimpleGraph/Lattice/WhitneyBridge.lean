/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanBridgeCycle
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The faithful face-region graph

The face-region graph of a graph `G` of `ℤ²` joins two adjacent faces unless the primal edge they
share lies in `G`. For the unit square its face `(0, 0)` is isolated, giving a bounded region (the
rotated region graph of `PlanarFaceGeometric`, by contrast, is connected for the unit square). The
file also states the cut–cycle duality `whb_CorrectWhitney` for this graph.

## Main definitions

* `StatMech.Lattice.whb_faceRegion G`: the graph on faces of `ℤ²` joining adjacent faces whose
  shared primal edge is not an edge of `G`.
* `StatMech.Lattice.whb_CorrectWhitney`: for every graph `H` and lattice edge `pq` outside `H`, `p`
  and `q` are connected in `H` iff deleting the dual edge across `pq` disconnects its ends in the
  face-region graph of `H`.

## Main results

* `StatMech.Lattice.whb_faceRegion_interior_supp`: in the faithful face-region graph of the unit
  square, the face `(0, 0)` is a component by itself.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

theorem whb_imageGraph_square :
    imageGraph jbc_Pce = jei_pushGraph jbc_Pce jbc_cyc4 :=
  (jei_pushGraph_G jbc_Pce).symm

theorem whb_reg_adj_of_straddle_ym1 {f g : Site 2}
    (hadj : (hypercubicLattice 2).Adj f g) (h : (rot90Inv f) 1 = -1 ∨ (rot90Inv g) 1 = -1) :
    (regionGraph (imageGraph jbc_Pce)).Adj f g := by
  rw [regionGraph_adj]
  refine ⟨hadj, ?_⟩
  rw [whb_imageGraph_square]
  rcases h with h | h
  · exact jbc_not_contour_ym1 h
  · exact jbc_not_contour_ym1' h

theorem whb_square_faceCount : faceCount jbc_cyc4 = 2 := by
  have hV : Nat.card (Fin 4) = 4 := by simp
  have hE : jbc_cyc4.edgeSet.ncard = 4 := by
    have : jbc_cyc4.edgeSet = {s(0, 1), s(1, 2), s(2, 3), s(3, 0)} := by
      ext e; obtain ⟨u, v⟩ := e
      rw [SimpleGraph.mem_edgeSet, jbc_cyc4_adj]
      constructor
      · intro h; fin_cases u <;> fin_cases v <;>
          simp_all [jbc_cyc4Rel]
      · intro h; fin_cases u <;> fin_cases v <;>
          simp_all [jbc_cyc4Rel]
    rw [this]
    rw [Set.ncard_eq_toFinset_card']
    decide
  have hC : Nat.card jbc_cyc4.ConnectedComponent = 1 := by
    have hconn : ∀ i j : Fin 4, jbc_cyc4.Reachable i j := by
      have a01 : jbc_cyc4.Adj 0 1 := by rw [jbc_cyc4_adj]; decide
      have a12 : jbc_cyc4.Adj 1 2 := by rw [jbc_cyc4_adj]; decide
      have a23 : jbc_cyc4.Adj 2 3 := by rw [jbc_cyc4_adj]; decide
      intro i j
      have r0 : ∀ k : Fin 4, jbc_cyc4.Reachable 0 k := by
        intro k; fin_cases k
        · exact Reachable.refl _
        · exact a01.reachable
        · exact a01.reachable.trans a12.reachable
        · exact a01.reachable.trans (a12.reachable.trans a23.reachable)
      exact (r0 i).symm.trans (r0 j)
    have hsub : Subsingleton jbc_cyc4.ConnectedComponent :=
      ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hconn a b))⟩
    rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, ⟨jbc_cyc4.connectedComponentMk 0⟩⟩
  unfold faceCount nullity
  rw [hE, hC, hV]

/-- The face-region graph of `G`: two adjacent faces of `ℤ²` are joined unless the primal edge
between them (`sharedPrimalEdge`) is an edge of `G`. This is the faithful planar dual
complement of `G`. -/
noncomputable def whb_faceRegion (G : SimpleGraph (Site 2)) : SimpleGraph (Site 2) where
  Adj f g := (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet
  symm := by
    refine ⟨?_⟩
    intro f g ⟨hadj, hs⟩
    exact ⟨hadj.symm, by rwa [sharedPrimalEdge_comm_of_adj hadj] at hs⟩
  loopless := ⟨fun f h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem whb_faceRegion_adj (G : SimpleGraph (Site 2)) (f g : Site 2) :
    (whb_faceRegion G).Adj f g ↔
      (hypercubicLattice 2).Adj f g ∧ sharedPrimalEdge f g ∉ G.edgeSet := Iff.rfl

theorem whb_square_edge_mem {u v : Fin 4} (h : jbc_cyc4.Adj u v) :
    s(jbc_csq u, jbc_csq v) ∈ (imageGraph jbc_Pce).edgeSet := by
  rw [SimpleGraph.mem_edgeSet, imageGraph_adj]
  exact ⟨u, v, h, rfl, rfl⟩

theorem whb_faceRegion_interior_isolated (g : Site 2) :
    ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g := by
  rintro ⟨hadj, hshared⟩
  apply hshared
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hg : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
  have h00 : (![0, 0] : Site 2) 0 = 0 := rfl
  have h01 : (![0, 0] : Site 2) 1 = 0 := rfl
  rw [h00, h01] at hadj
  have : (g 0 = 1 ∧ g 1 = 0) ∨ (g 0 = -1 ∧ g 1 = 0) ∨
      (g 0 = 0 ∧ g 1 = 1) ∨ (g 0 = 0 ∧ g 1 = -1) := by omega
  rcases this with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![1, 0] : Site 2) = ![(0 : ℤ) + 1, 0] by norm_num, sharedPrimalEdge_right]
    exact whb_square_edge_mem (u := 1) (v := 2) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![-1, 0] : Site 2) = ![(0 : ℤ) - 1, 0] by norm_num, sharedPrimalEdge_left]
    exact whb_square_edge_mem (u := 0) (v := 3) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![0, 1] : Site 2) = ![(0 : ℤ), 0 + 1] by norm_num, sharedPrimalEdge_top]
    exact whb_square_edge_mem (u := 3) (v := 2) (by rw [jbc_cyc4_adj]; decide)
  · rw [hg, hx, hy, show (![0, 0] : Site 2) = ![(0 : ℤ), 0] from rfl]
    rw [show (![0, -1] : Site 2) = ![(0 : ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    exact whb_square_edge_mem (u := 0) (v := 1) (by rw [jbc_cyc4_adj]; decide)

theorem whb_faceRegion_interior_supp :
    ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp = {![0, 0]} := by
  ext x
  rw [ConnectedComponent.mem_supp_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    rw [ConnectedComponent.eq] at h
    obtain ⟨w⟩ := h.symm
    cases w with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (whb_faceRegion_interior_isolated _)
  · rintro rfl; rfl

theorem whb_faceRegion_interior_bounded :
    ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite := by
  rw [whb_faceRegion_interior_supp]; exact Set.finite_singleton _

/-- **Whitney's cut–cycle duality** for subgraphs of `ℤ²` (H. Whitney, *Planar graphs*, 1933):
for every `H` and lattice edge `pq` not in `H`, with `fg` the dual edge across `pq`, the
endpoints `p` and `q` are connected in `H` iff `f` and `g` are disconnected in the
face-region graph of `H` with `fg` deleted. -/
def whb_CorrectWhitney : Prop :=
  ∀ (H : SimpleGraph (Site 2)) (p q f g : Site 2),
    (hypercubicLattice 2).Adj p q → s(p, q) ∉ H.edgeSet →
    (hypercubicLattice 2).Adj f g → sharedPrimalEdge f g = s(p, q) →
    (H.Reachable p q ↔
      ¬ ((whb_faceRegion H).deleteEdges {s(f, g)}).Reachable f g)

theorem whb_correctModel_square_separates :
    (∀ g, ¬ (whb_faceRegion (imageGraph jbc_Pce)).Adj ![0, 0] g) ∧
      ((whb_faceRegion (imageGraph jbc_Pce)).connectedComponentMk ![0, 0]).supp.Finite :=
  ⟨whb_faceRegion_interior_isolated, whb_faceRegion_interior_bounded⟩

end Lattice

end StatMech
