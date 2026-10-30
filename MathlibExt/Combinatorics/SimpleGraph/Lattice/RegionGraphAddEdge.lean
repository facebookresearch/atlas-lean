/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarDual
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.PlanarFaceGeometric
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanOuterFaceUnique
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.CycleRank
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.EulerGeneral
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.JordanCycleRank

/-!
# Adding one edge to a subgraph of `ℤ²` and its region graph

Adding the edge `{p, q}` to a graph `G` of the square lattice removes one edge, `crossEdge s(p, q)`,
from its region graph. Removing one edge from a graph either keeps its number of components or
increases it by one, according to whether the edge lies on a cycle. These are the inductive steps
for counting regions edge by edge.

## Main results

* `StatMech.Lattice.jsf_card_components_sup_edge_merge`: adding an edge between two components
  merges them; see also `StatMech.Lattice.card_components_sup_edge_of_not_reachable`, which assumes
  a finite vertex type instead of finitely many components.
* `StatMech.Lattice.jsf_regionGraph_sup_edge`: the region graph of `G ⊔ edge p q` is the region
  graph of `G` with `crossEdge s(p, q)` deleted.
* `StatMech.Lattice.jsf_dual_delete_dichotomy`: the component count of the region graph changes by
  zero or one when an edge is added.
-/

@[expose] public section

open SimpleGraph Set

namespace StatMech

namespace Lattice

/-- Adding an edge between two components merges them. This assumes only finitely many
components; see also `StatMech.Lattice.card_components_sup_edge_of_not_reachable` for finite
vertex types. -/
theorem jsf_card_components_sup_edge_merge {V : Type*}
    (G : SimpleGraph V) [Finite G.ConnectedComponent] {a b : V} (hab : ¬ G.Reachable a b) :
    Nat.card (G ⊔ edge a b).ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
  classical
  let f : G.ConnectedComponent → (G ⊔ edge a b).ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE (le_sup_left : G ≤ G ⊔ edge a b))
  let cb := G.connectedComponentMk b
  let ca := G.connectedComponentMk a
  have hid : ∀ x : V, (Hom.ofLE (le_sup_left : G ≤ G ⊔ edge a b)) x = x := fun _ => rfl
  have key : ∀ x y : V, (f (G.connectedComponentMk x) = f (G.connectedComponentMk y)) ↔
      (G.Reachable x y ∨ (G.Reachable x a ∧ G.Reachable b y) ∨
        (G.Reachable x b ∧ G.Reachable a y)) := by
    intro x y
    change (G ⊔ edge a b).connectedComponentMk _ = (G ⊔ edge a b).connectedComponentMk _ ↔ _
    rw [hid, hid, ConnectedComponent.eq, reachable_sup_edge]
  have hane : ca ≠ cb := by simp only [ca, cb, Ne, ConnectedComponent.eq]; exact hab
  have hfeq : f ca = f cb := by
    rw [show ca = G.connectedComponentMk a from rfl, show cb = G.connectedComponentMk b from rfl,
      key]
    right; left; exact ⟨Reachable.refl _, Reachable.refl _⟩
  let φ : {c : G.ConnectedComponent // c ≠ cb} → (G ⊔ edge a b).ConnectedComponent := fun c => f c.1
  have hφsurj : Function.Surjective φ := by
    intro d
    obtain ⟨c, hc⟩ := ConnectedComponent.surjective_map_ofLE (le_sup_left : G ≤ G ⊔ edge a b) d
    by_cases hccb : c = cb
    · exact ⟨⟨ca, hane⟩, by change f ca = d; rw [hfeq]; exact hccb ▸ hc⟩
    · exact ⟨⟨c, hccb⟩, hc⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    simp only [φ] at h
    refine Subtype.ext ?_
    revert hc hc' h
    refine ConnectedComponent.ind₂ (fun x y hx hy h => ?_) c c'
    rw [key] at h
    rcases h with hg | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ConnectedComponent.eq]; exact hg
    · exfalso; apply hy; show G.connectedComponentMk y = cb
      rw [show cb = G.connectedComponentMk b from rfl, ConnectedComponent.eq]; exact h2.symm
    · exfalso; apply hx; show G.connectedComponentMk x = cb
      rw [show cb = G.connectedComponentMk b from rfl, ConnectedComponent.eq]; exact h1
  have hcard : Nat.card {c : G.ConnectedComponent // c ≠ cb}
      = Nat.card (G ⊔ edge a b).ConnectedComponent :=
    Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)
  rw [← hcard]; exact card_subtype_ne_add_one cb

theorem jsf_mem_edgeSet_edge {p q : Site 2} (hpq : p ≠ q) (e : Sym2 (Site 2)) :
    e ∈ (edge p q).edgeSet ↔ e = s(p, q) := by
  obtain ⟨x, y⟩ := e
  rw [SimpleGraph.mem_edgeSet, edge_adj]
  constructor
  · rintro ⟨h, _⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [Sym2.eq_swap]
  · intro heq
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Or.inl ⟨rfl, rfl⟩, hpq⟩
    · exact ⟨Or.inr ⟨rfl, rfl⟩, hpq.symm⟩

theorem jsf_regionGraph_sup_edge (G : SimpleGraph (Site 2)) {p q : Site 2} (hpq : p ≠ q) :
    regionGraph (G ⊔ edge p q) = (regionGraph G).deleteEdges {crossEdge s(p, q)} := by
  ext f g
  rw [regionGraph_adj, deleteEdges_adj, regionGraph_adj]
  rw [SimpleGraph.edgeSet_sup, Set.mem_union, not_or]
  have hkey : crossEdge.symm s(f, g) ∈ (edge p q).edgeSet ↔ s(f, g) = crossEdge s(p, q) := by
    rw [jsf_mem_edgeSet_edge hpq, Equiv.symm_apply_eq]
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hadj, hnG, hnE⟩
    exact ⟨⟨hadj, hnG⟩, fun heq => hnE (hkey.mpr heq)⟩
  · rintro ⟨⟨hadj, hnG⟩, hne⟩
    exact ⟨hadj, hnG, fun hE => hne (hkey.mp hE)⟩

theorem jsf_regionGraph_bot :
    regionGraph (⊥ : SimpleGraph (Site 2)) = hypercubicLattice 2 := by
  ext f g
  rw [regionGraph_adj, SimpleGraph.edgeSet_bot]
  simp

theorem jsf_dual_delete_dichotomy (G : SimpleGraph (Site 2)) {p q f g : Site 2}
    [Finite (regionGraph G).ConnectedComponent]
    [Finite (regionGraph (G ⊔ edge p q)).ConnectedComponent]
    (hpq : p ≠ q)
    (hfg : crossEdge s(p, q) = s(f, g)) (hpres : crossEdge s(p, q) ∈ (regionGraph G).edgeSet) :
    (((regionGraph G).deleteEdges {crossEdge s(p, q)}).Reachable f g →
        Nat.card (regionGraph (G ⊔ edge p q)).ConnectedComponent
          = Nat.card (regionGraph G).ConnectedComponent) ∧
      (¬ ((regionGraph G).deleteEdges {crossEdge s(p, q)}).Reachable f g →
        Nat.card (regionGraph (G ⊔ edge p q)).ConnectedComponent
          = Nat.card (regionGraph G).ConnectedComponent + 1) := by
  classical
  set RG := regionGraph G with hRG
  set RGdel := RG.deleteEdges {crossEdge s(p, q)} with hRGdel_def
  have hRGdel : regionGraph (G ⊔ edge p q) = RGdel :=
    jsf_regionGraph_sup_edge G hpq
  have hfinDel : Finite RGdel.ConnectedComponent :=
    hRGdel ▸ (inferInstance : Finite (regionGraph (G ⊔ edge p q)).ConnectedComponent)
  have hpres' : s(f, g) ∈ RG.edgeSet := by rw [hfg] at hpres; exact hpres
  have hdecomp : RG = RGdel ⊔ edge f g := by
    rw [hRGdel_def, hfg]
    exact deleteEdges_sup_edge_eq RG f g (by rw [← hfg]; exact hpres)
  refine ⟨fun hr => ?_, fun hr => ?_⟩
  · rw [hRGdel]
    have hkeep := card_components_sup_edge_of_reachable RGdel f g hr
    conv_rhs => rw [hdecomp]
    exact hkeep.symm
  · rw [hRGdel]
    have hmerge := jsf_card_components_sup_edge_merge RGdel (a := f) (b := g) hr
    rw [hdecomp]
    omega

end Lattice

end StatMech
