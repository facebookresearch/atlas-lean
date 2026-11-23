/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoundaryConditions

/-!
# Tests for `MathlibExt.Combinatorics.SimpleGraph.Lattice.BoundaryConditions`

Computes cluster counts on the single edge `⊤ : SimpleGraph (Fin 2)` with both vertices on the
boundary. With the edge closed there are two free clusters and one wired cluster (the boundary is
wired together), so `numClusters_wired_le_free` is strict here; with the edge open both counts are
one. Also checks the distinctness of the three boundary conditions, that the periodic count is the
free count of the given graph, and the adjacency of `openGraph`, `boundaryCliqueGraph`, and
`wiredGraph`.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.BoundaryConditions

open _root_.StatMech _root_.StatMech.Lattice

/-- Number of components of a graph whose vertices are pairwise non-reachable. -/
theorem card_components_of_not_reachable {V : Type*} [Finite V] (G : SimpleGraph V)
    (h : ∀ x y, G.Reachable x y → x = y) : Nat.card G.ConnectedComponent = Nat.card V := by
  refine Nat.card_congr (Equiv.ofBijective G.connectedComponentMk ⟨fun x y hxy => ?_, ?_⟩).symm
  · exact h x y (SimpleGraph.ConnectedComponent.eq.mp hxy)
  · intro c; induction c using SimpleGraph.ConnectedComponent.ind with | h v => exact ⟨v, rfl⟩

/-- A connected graph has exactly one component. -/
theorem card_components_of_connected {V : Type*} {G : SimpleGraph V} (h : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  have := h.preconnected.subsingleton_connectedComponent
  have : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk h.nonempty.some⟩
  exact Nat.card_of_subsingleton (G.connectedComponentMk h.nonempty.some)

-- The three boundary conditions are distinct.
example : BoundaryCondition.free ≠ BoundaryCondition.wired := BoundaryCondition.free_ne_wired
example : BoundaryCondition.wired ≠ BoundaryCondition.periodic :=
  BoundaryCondition.wired_ne_periodic

/-- Every vertex of `Fin 2` is on the boundary. -/
abbrev allBdry : Fin 2 → Prop := fun _ => True

-- `openGraph` keeps exactly the open edges: the closed configuration gives no edges.
example : ¬ (openGraph (⊤ : SimpleGraph (Fin 2)) (fun _ => false)).Adj 0 1 := by
  simp [openGraph_adj]

-- `boundaryCliqueGraph` joins distinct boundary vertices.
example : (boundaryCliqueGraph allBdry).Adj 0 1 := by
  simp [boundaryCliqueGraph_adj]

-- `wiredGraph` joins the two boundary vertices even when the edge is closed.
example : (wiredGraph (⊤ : SimpleGraph (Fin 2)) allBdry (fun _ => false)).Adj 0 1 := by
  simp [wiredGraph_adj]

-- Closed edge, free boundary condition: two clusters.
example : numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .free (fun _ => false) = 2 := by
  rw [numClusters_free, numClustersFree]
  rw [card_components_of_not_reachable _ (fun x y hxy => ?_), Nat.card_eq_fintype_card,
    Fintype.card_fin]
  have hbot : openGraph (⊤ : SimpleGraph (Fin 2)) (fun _ => false) = ⊥ := by
    ext a b; simp [openGraph_adj]
  rw [hbot, SimpleGraph.reachable_bot] at hxy
  exact hxy

-- Closed edge, wired boundary condition: one cluster.
example : numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .wired (fun _ => false) = 1 := by
  rw [numClusters_wired, numClustersWired]
  apply card_components_of_connected
  have htop : wiredGraph (⊤ : SimpleGraph (Fin 2)) allBdry (fun _ => false) = ⊤ := by
    ext a b; simp [wiredGraph_adj]
  rw [htop]; exact SimpleGraph.connected_top

-- Open edge, free boundary condition: one cluster.
example : numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .free (fun _ => true) = 1 := by
  rw [numClusters_free, numClustersFree]
  apply card_components_of_connected
  have htop : openGraph (⊤ : SimpleGraph (Fin 2)) (fun _ => true) = ⊤ := by
    ext a b; simp [openGraph_adj]
  rw [htop]; exact SimpleGraph.connected_top

-- `numClusters_wired_le_free` at the closed edge: `1 ≤ 2`.
example : numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .wired (fun _ => false)
    ≤ numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .free (fun _ => false) :=
  numClusters_wired_le_free _ _ _

-- The periodic count is the free count of the graph passed in (the torus must be built into `G`).
example (ω : Sym2 (Fin 2) → Bool) :
    numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .periodic ω
      = numClusters (⊤ : SimpleGraph (Fin 2)) allBdry .free ω := by
  rw [numClusters_periodic, numClusters_free]

end MathlibExtTest.StatMech.Combinatorics.SimpleGraph.Lattice.BoundaryConditions
