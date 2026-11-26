/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Graph.GraphMinor
public import MathlibExt.Combinatorics.SimpleGraph.TreeDecomposition

/-!
# Tree-width of graph minors

A tree-width bound for a finite graph passes to each of its minors. Deletions pull bags back
along an injection, and contracting an edge takes the image of each bag in the quotient graph.
-/

public section

namespace MetaMathlibExt.IsMinor

open SimpleGraph

universe u

private theorem of_injective_hom {H G : FinGraph.{u}} (f : H.V → G.V) (hf : Function.Injective f)
    (hadj : ∀ u v, H.G.Adj u v → G.G.Adj (f u) (f v)) {k : ℕ}
    (hG : G.G.HasTreewidthAtMost k) : H.G.HasTreewidthAtMost k := by
  obtain ⟨D, hD⟩ := hG
  refine ⟨{ ι := D.ι, finite := D.finite, T := D.T, isTree := D.isTree
            bag := fun t => f ⁻¹' D.bag t
            cover := fun v => D.cover (f v)
            edge_mem := fun u v h => D.edge_mem _ _ (hadj u v h)
            coherent := fun s t i p hp hi _ hx => D.coherent s t i p hp hi hx }, ?_⟩
  intro t
  refine le_trans ?_ (hD t)
  exact Set.encard_le_encard_of_injOn (f := f) (fun _ hx => hx) hf.injOn

/-- If two vertices occur together in a bag, the union of their occurrence subtrees contains
the path between any bag of the first vertex and any bag of the second. -/
private theorem mem_bag_or_mem_bag {G : FinGraph} (D : G.G.TreeDecomposition)
    {x y : G.V} {s t i j : D.ι} (hxs : x ∈ D.bag s) (hyt : y ∈ D.bag t)
    (hxj : x ∈ D.bag j) (hyj : y ∈ D.bag j)
    (p : D.T.Walk s t) (hp : p.IsPath) (hi : i ∈ p.support) :
    x ∈ D.bag i ∨ y ∈ D.bag i := by
  classical
  obtain ⟨q, hq⟩ := (D.isTree.existsUnique_path s j).exists
  obtain ⟨r, hr⟩ := (D.isTree.existsUnique_path j t).exists
  -- Shortening the walk through the common bag gives the unique path from s to t.
  have heq : p = (q.append r).toPath.val :=
    Subtype.mk.inj ((D.isTree.isAcyclic.subsingleton_path s t).elim ⟨p, hp⟩ (q.append r).toPath)
  have hi' := (q.append r).support_toPath_subset_support (heq ▸ hi)
  exact ((Walk.mem_support_append_iff q r).mp hi').imp
    (fun h => D.coherent s j i q hq h ⟨hxs, hxj⟩)
    (fun h => D.coherent j t i r hr h ⟨hyj, hyt⟩)

private theorem of_minorStep {H G : FinGraph.{u}} (h : MinorStep H G) {k : ℕ}
    (hG : G.G.HasTreewidthAtMost k) : H.G.HasTreewidthAtMost k := by
  cases h with
  | iso e => exact of_injective_hom e e.injective (fun _ _ => e.map_adj_iff.mpr) hG
  | deleteVertex f h _ _ =>
    exact of_injective_hom f f.injective (fun u v => (h u v).mp) hG
  | deleteEdge e h _ _ _ _ _ => exact of_injective_hom e e.injective h hG
  | contractEdge f hsurj a b hab _ _ hsingle hadj =>
    obtain ⟨D, hD⟩ := hG
    refine ⟨{ ι := D.ι, finite := D.finite, T := D.T, isTree := D.isTree
              bag := fun t => f '' D.bag t
              cover := ?_, edge_mem := ?_, coherent := ?_ }, ?_⟩
    · intro v
      obtain ⟨x, rfl⟩ := hsurj v
      obtain ⟨t, hx⟩ := D.cover x
      exact ⟨t, x, hx, rfl⟩
    · intro u v huv
      obtain ⟨x, y, rfl, rfl, hxy⟩ := ((hadj u v).mp huv).2
      obtain ⟨t, hx, hy⟩ := D.edge_mem x y hxy
      exact ⟨t, ⟨x, hx, rfl⟩, y, hy, rfl⟩
    · rintro s t i p hp hi _ ⟨⟨x, hxs, rfl⟩, y, hyt, hyx⟩
      rcases hsingle x y hyx.symm with rfl | h
      · exact ⟨_, D.coherent s t i p hp hi ⟨hxs, hyt⟩, rfl⟩
      · obtain ⟨j, hxj, hyj⟩ := D.edge_mem x y (by
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hab
          · exact hab.symm)
        rcases mem_bag_or_mem_bag D hxs hyt hxj hyj p hp hi with hx | hy
        · exact ⟨x, hx, rfl⟩
        · exact ⟨y, hy, hyx⟩
    · exact fun t => (Set.encard_image_le f (D.bag t)).trans (hD t)

/-- **Tree-width does not increase under taking minors.** If `H` is a minor of the finite graph
`G` and `G` has tree-width at most `k`, then so does `H` (Diestel, *Graph Theory*, 6th ed.,
Lemma 12.4.1, from Lemmas 12.3.2 and 12.3.3). -/
theorem hasTreewidthAtMost {H G : FinGraph} (h : IsMinor H G) {k : ℕ}
    (hG : G.G.HasTreewidthAtMost k) : H.G.HasTreewidthAtMost k := by
  induction h with
  | refl => exact hG
  | tail _ step ih => exact ih (of_minorStep step hG)

end MetaMathlibExt.IsMinor
