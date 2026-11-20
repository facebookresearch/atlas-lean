/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKRectTorusRibbonReduction

open Finset SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section



theorem fkRectOpenGraph_configurationOfEdges_insert
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    {p q : R.Vertex} (he : fkRectTorusIndexedEdge R e = s(p, q)) :
    fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F)) =
      fkRectOpenGraph R (fkRectConfigurationOfEdges R F) ⊔ edge p q := by
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact fkRectTorusIndexedEdge_ne_diag R e p he
  ext x y
  simp only [fkRectOpenGraph_configurationOfEdges_adj, Finset.mem_insert,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨a, rfl | ha, hxy⟩
    · right
      rw [he] at hxy
      rcases Sym2.eq_iff.mp hxy with hxy | hxy
      · exact ⟨Or.inl ⟨hxy.1.symm, hxy.2.symm⟩, by
          simpa [hxy.1, hxy.2] using hpq⟩
      · exact ⟨Or.inr ⟨hxy.2.symm, hxy.1.symm⟩, by
          simpa [hxy.1, hxy.2] using hpq.symm⟩
    · exact Or.inl ⟨a, ha, hxy⟩
  · rintro (hxy | hxy)
    · obtain ⟨a, ha, hxy⟩ := hxy
      exact ⟨a, Or.inr ha, hxy⟩
    · exact ⟨e, Or.inl rfl, by
        rw [he, Sym2.eq_iff]
        rcases hxy.1 with hxy | hxy
        · exact Or.inl ⟨hxy.1.symm, hxy.2.symm⟩
        · exact Or.inr ⟨hxy.2.symm, hxy.1.symm⟩⟩



theorem fkRectFinsetClusterCount_insert_of_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    {p q : R.Vertex} (he : fkRectTorusIndexedEdge R e = s(p, q))
    (hreach : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable p q) :
    fkRectFinsetClusterCount R (insert e F) =
      fkRectFinsetClusterCount R F := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  have hgraph := fkRectOpenGraph_configurationOfEdges_insert R F e he
  have hcard := card_components_sup_edge_of_reachable G p q hreach
  unfold fkRectFinsetClusterCount fkRectNumClusters
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  calc
    Nat.card (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R (insert e F))).ConnectedComponent =
        Nat.card (G ⊔ edge p q).ConnectedComponent := by
      exact Nat.card_congr (Equiv.cast (congrArg
        (fun H : SimpleGraph R.Vertex => H.ConnectedComponent) hgraph))
    _ = Nat.card G.ConnectedComponent := hcard



theorem fkRectFinsetClusterCount_insert_of_not_reachable
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    {p q : R.Vertex} (he : fkRectTorusIndexedEdge R e = s(p, q))
    (hreach : ¬ (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Reachable p q) :
    fkRectFinsetClusterCount R (insert e F) + 1 =
      fkRectFinsetClusterCount R F := by
  let G := fkRectOpenGraph R (fkRectConfigurationOfEdges R F)
  have hgraph := fkRectOpenGraph_configurationOfEdges_insert R F e he
  have hcard := card_components_sup_edge_of_not_reachable G p q hreach
  unfold fkRectFinsetClusterCount fkRectNumClusters
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  calc
    Nat.card (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R (insert e F))).ConnectedComponent + 1 =
        Nat.card (G ⊔ edge p q).ConnectedComponent + 1 := by
      congr 1
      exact Nat.card_congr (Equiv.cast (congrArg
        (fun H : SimpleGraph R.Vertex => H.ConnectedComponent) hgraph))
    _ = Nat.card G.ConnectedComponent := hcard

end

end StatMech.FrontierD
