/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.FKMedialToggleGraph
import Code.Lattice.EulerComponentCount
import Code.Lattice.JordanEnclosure

open SimpleGraph Set

namespace StatMech.FrontierD

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_components_sup_edge_le (G : SimpleGraph V) (a b : V) :
    Nat.card (G ⊔ edge a b).ConnectedComponent ≤
      Nat.card G.ConnectedComponent := by
  by_cases hab : G.Reachable a b
  · rw [card_components_sup_edge_of_reachable G a b hab]
  · have h := card_components_sup_edge_of_not_reachable G a b hab
    omega

private theorem switch_walk_avoids_other_component
    (G : SimpleGraph V) {a b c d : V}
    (hdisc : ¬ G.Reachable a c) (p : G.Walk c d) :
    s(a, b) ∉ p.edges := by
  intro hedge
  have ha : a ∈ p.support := p.fst_mem_support_of_mem_edges hedge
  have hca : G.Reachable c a := (p.takeUntil a ha).reachable
  exact hdisc hca.symm

private theorem switch_delete_two_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj] (heven : ∀ x, Even (G.degree x))
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdisc : ¬ G.Reachable a c) :
    let K := G.deleteEdges {s(a, b), s(c, d)}
    K.Reachable a b ∧ K.Reachable c d := by
  classical
  have hrab : (G.deleteEdges {s(a, b)}).Reachable a b :=
    EvenDegree.reachable_deleteEdges_of_even G heven hab
  have hrcd : (G.deleteEdges {s(c, d)}).Reachable c d :=
    EvenDegree.reachable_deleteEdges_of_even G heven hcd
  obtain ⟨pab, hpab⟩ :=
    (reachable_deleteEdges_iff_exists_walk (G := G)).mp hrab
  obtain ⟨pcd, hpcd⟩ :=
    (reachable_deleteEdges_iff_exists_walk (G := G)).mp hrcd
  have habAvoid : s(c, d) ∉ pab.edges := by
    intro hedge
    have hc : c ∈ pab.support := pab.fst_mem_support_of_mem_edges hedge
    exact hdisc (pab.takeUntil c hc).reachable
  have hcdAvoid : s(a, b) ∉ pcd.edges :=
    switch_walk_avoids_other_component G hdisc pcd
  constructor
  · exact ⟨pab.toDeleteEdges {s(a, b), s(c, d)} (by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        exact hpab (h ▸ he)
      · intro h
        exact habAvoid (h ▸ he))⟩
  · exact ⟨pcd.toDeleteEdges {s(a, b), s(c, d)} (by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      constructor
      · intro h
        exact hcdAvoid (h ▸ he)
      · intro h
        exact hpcd (h ▸ he))⟩

private theorem switch_delete_two_card_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] (heven : ∀ x, Even (G.degree x))
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdisc : ¬ G.Reachable a c) :
    Nat.card (G.deleteEdges {s(a, b), s(c, d)}).ConnectedComponent =
      Nat.card G.ConnectedComponent := by
  classical
  let G1 := G.deleteEdges {s(a, b)}
  let K := G.deleteEdges {s(a, b), s(c, d)}
  have hrab : (G.deleteEdges {s(a, b)}).Reachable a b :=
    EvenDegree.reachable_deleteEdges_of_even G heven hab
  have hcard1 := ecc_deleteEdge_card_nonbridge G
    (by simpa only [SimpleGraph.mem_edgeSet] using hab) hrab
  have hne : s(c, d) ≠ s(a, b) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact hdisc (by simpa [h.1] using (Reachable.refl (G := G) a))
    · exact hdisc (by simpa [h.1] using hab.reachable)
  have heG1 : s(c, d) ∈ G1.edgeSet := by
    rw [SimpleGraph.mem_edgeSet, SimpleGraph.deleteEdges_adj]
    exact ⟨hcd, by simpa [hne]⟩
  have hrK := (switch_delete_two_reachable G heven hab hcd hdisc).2
  have hdel : G1.deleteEdges {s(c, d)} = K := by
    unfold G1 K
    rw [SimpleGraph.deleteEdges_deleteEdges]
    congr 1
  have hr2 : (G1.deleteEdges {s(c, d)}).Reachable c d := by
    rwa [hdel]
  have hcard2 := ecc_deleteEdge_card_nonbridge G1 heG1 hr2
  rw [hdel] at hcard2
  exact hcard2.trans hcard1




theorem card_components_twoEdgeSwitch_le_add_one
    (G : SimpleGraph V) [DecidableRel G.Adj] (heven : ∀ x, Even (G.degree x))
    {a b c d : V} (hab : G.Adj a b) :
    let H := (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent + 1 := by
  classical
  let G1 := G.deleteEdges {s(a, b)}
  let K := G.deleteEdges {s(a, b), s(c, d)}
  let J := K ⊔ edge a d
  let H := J ⊔ edge c b
  have hrab : G1.Reachable a b :=
    EvenDegree.reachable_deleteEdges_of_even G heven hab
  have hcard1 : Nat.card G1.ConnectedComponent =
      Nat.card G.ConnectedComponent :=
    ecc_deleteEdge_card_nonbridge G
      (by simpa only [SimpleGraph.mem_edgeSet] using hab) hrab
  have hdel : G1.deleteEdges {s(c, d)} = K := by
    unfold G1 K
    rw [SimpleGraph.deleteEdges_deleteEdges]
    congr 1
  have hcardK := ecc_deleteEdge_card_le G1 s(c, d)
  rw [hdel, hcard1] at hcardK
  have hcardJ : Nat.card J.ConnectedComponent ≤
      Nat.card K.ConnectedComponent :=
    card_components_sup_edge_le K a d
  have hcardH : Nat.card H.ConnectedComponent ≤
      Nat.card J.ConnectedComponent :=
    card_components_sup_edge_le J c b
  change Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent + 1
  omega





theorem card_components_twoEdgeSwitch_of_not_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj] (heven : ∀ x, Even (G.degree x))
    {a b c d : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdisc : ¬ G.Reachable a c) :
    let H := (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b
    Nat.card H.ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
  classical
  let K := G.deleteEdges {s(a, b), s(c, d)}
  let J := K ⊔ edge a d
  let H := J ⊔ edge c b
  have hK := switch_delete_two_reachable G heven hab hcd hdisc
  have hKle : K ≤ G := (SimpleGraph.deleteEdges_le _)
  have had : ¬ K.Reachable a d := by
    intro had
    have hadG : G.Reachable a d := had.mono hKle
    exact hdisc (hadG.trans hcd.symm.reachable)
  have hcardJ := card_components_sup_edge_of_not_reachable K a d had
  have hnead : a ≠ d := by
    intro h
    exact had (by simpa [h] using (Reachable.refl (G := K) a))
  have hcb : J.Reachable c b := by
    have hda : J.Reachable d a := Adj.reachable (by
      rw [SimpleGraph.sup_adj]
      right
      rw [SimpleGraph.edge_adj]
      exact ⟨Or.inr ⟨rfl, rfl⟩, hnead.symm⟩)
    have hcdJ : J.Reachable c d := hK.2.mono le_sup_left
    have habJ : J.Reachable a b := hK.1.mono le_sup_left
    exact hcdJ.trans (hda.trans habJ)
  have hcardH := card_components_sup_edge_of_reachable J c b hcb
  have hcardK := switch_delete_two_card_eq G heven hab hcd hdisc
  change Nat.card H.ConnectedComponent + 1 = Nat.card G.ConnectedComponent
  rw [hcardH, hcardJ, hcardK]

end

end StatMech.FrontierD
