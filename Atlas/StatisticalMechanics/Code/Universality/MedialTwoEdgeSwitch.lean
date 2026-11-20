/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKMedialSwitchCount










open SimpleGraph Set

namespace StatMech.Universality

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]



def medialTwoEdgeSwitch (G : SimpleGraph V) (a b c d : V) : SimpleGraph V :=
  ((G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b)


theorem medialTwoEdgeSwitch_swap_pairs (G : SimpleGraph V) (a b c d : V) :
    medialTwoEdgeSwitch G c d a b = medialTwoEdgeSwitch G a b c d := by
  ext u v
  simp [medialTwoEdgeSwitch, SimpleGraph.deleteEdges_adj,
    SimpleGraph.sup_adj, SimpleGraph.edge_adj, or_comm, or_left_comm,
    or_assoc]

private theorem medial_delete_two_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : forall x, Even (G.degree x))
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
  have hcdAvoid : s(a, b) ∉ pcd.edges := by
    intro hedge
    have ha : a ∈ pcd.support := pcd.fst_mem_support_of_mem_edges hedge
    exact hdisc (pcd.takeUntil a ha).reachable.symm
  constructor
  · exact ⟨pab.toDeleteEdges {s(a, b), s(c, d)} (by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hpab (h ▸ he), fun h => habAvoid (h ▸ he)⟩)⟩
  · exact ⟨pcd.toDeleteEdges {s(a, b), s(c, d)} (by
      intro e he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hcdAvoid (h ▸ he), fun h => hpcd (h ▸ he)⟩)⟩

private theorem reachable_of_adj_reachable {G K : SimpleGraph V}
    (hstep : forall {u v}, G.Adj u v -> K.Reachable u v)
    {x y : V} (hxy : G.Reachable x y) : K.Reachable x y := by
  obtain ⟨p⟩ := hxy
  induction p with
  | nil => exact Reachable.refl _
  | cons huv p ih => exact (hstep huv).trans ih

private theorem reachable_delete_two_of_reachable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : forall x, Even (G.degree x))
    {a b c d x y : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdisc : ¬ G.Reachable a c) (hxy : G.Reachable x y) :
    (G.deleteEdges {s(a, b), s(c, d)}).Reachable x y := by
  classical
  let K := G.deleteEdges {s(a, b), s(c, d)}
  have hK := medial_delete_two_reachable G heven hab hcd hdisc
  apply reachable_of_adj_reachable (K := K) (G := G) ?_ hxy
  intro u v huv
  by_cases habuv : s(u, v) = s(a, b)
  · rcases Sym2.eq_iff.mp habuv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hK.1
    · exact hK.1.symm
  by_cases hcduv : s(u, v) = s(c, d)
  · rcases Sym2.eq_iff.mp hcduv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hK.2
    · exact hK.2.symm
  exact Adj.reachable (by
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨huv, by simp [habuv, hcduv]⟩)




theorem medialTwoEdgeSwitch_reachable_all_of_reachable_left
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : forall x, Even (G.degree x))
    {a b c d x : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdisc : ¬ G.Reachable a c) (hxa : G.Reachable x a) :
    (medialTwoEdgeSwitch G a b c d).Reachable x a ∧
      (medialTwoEdgeSwitch G a b c d).Reachable x b ∧
      (medialTwoEdgeSwitch G a b c d).Reachable x c ∧
      (medialTwoEdgeSwitch G a b c d).Reachable x d := by
  classical
  let K := G.deleteEdges {s(a, b), s(c, d)}
  let J := K ⊔ edge a d
  let H := J ⊔ edge c b
  have hK := medial_delete_two_reachable G heven hab hcd hdisc
  have hxaK : K.Reachable x a :=
    reachable_delete_two_of_reachable G heven hab hcd hdisc hxa
  have hxbK : K.Reachable x b := hxaK.trans hK.1
  have had : a ≠ d := by
    intro had
    subst d
    exact hdisc hcd.symm.reachable
  have hxdJ : J.Reachable x d := by
    apply hxaK.mono le_sup_left |>.trans
    exact Adj.reachable (by
      rw [SimpleGraph.sup_adj, SimpleGraph.edge_adj]
      exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, had⟩)
  have hxcJ : J.Reachable x c :=
    hxdJ.trans (hK.2.symm.mono le_sup_left)
  change H.Reachable x a ∧ H.Reachable x b ∧
    H.Reachable x c ∧ H.Reachable x d
  exact ⟨(hxaK.mono le_sup_left).mono le_sup_left,
    (hxbK.mono le_sup_left).mono le_sup_left,
    hxcJ.mono le_sup_left, hxdJ.mono le_sup_left⟩



theorem medialTwoEdgeSwitch_reachable_all_of_reachable_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : forall x, Even (G.degree x))
    {a b c d x : V} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hdisc : ¬ G.Reachable a c) (hxc : G.Reachable x c) :
    (medialTwoEdgeSwitch G a b c d).Reachable x a ∧
      (medialTwoEdgeSwitch G a b c d).Reachable x b ∧
      (medialTwoEdgeSwitch G a b c d).Reachable x c ∧
      (medialTwoEdgeSwitch G a b c d).Reachable x d := by
  classical
  have hdisc' : ¬ G.Reachable c a := fun h => hdisc h.symm
  have hall := medialTwoEdgeSwitch_reachable_all_of_reachable_left G heven
    hcd hab hdisc' hxc
  rw [medialTwoEdgeSwitch_swap_pairs] at hall
  exact ⟨hall.2.2.1, hall.2.2.2, hall.1, hall.2.1⟩





theorem medialTwoEdgeSwitch_reachable_iff_of_disjoint
    (G : SimpleGraph V) {a b c d x y : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hxa : ¬ G.Reachable x a) (hxc : ¬ G.Reachable x c) :
    (medialTwoEdgeSwitch G a b c d).Reachable x y ↔ G.Reachable x y := by
  classical
  constructor
  · intro hxy
    obtain ⟨p⟩ := hxy
    suffices hwalk : forall {u v : V},
        (medialTwoEdgeSwitch G a b c d).Walk u v ->
        G.Reachable x u -> G.Reachable x v by
      exact hwalk p (Reachable.refl _)
    intro u v p
    induction p with
    | nil => exact fun h => h
    | @cons u v w huv p ih =>
        intro hxu
        have hxv : G.Reachable x v := by
          change ((((G.deleteEdges {s(a, b), s(c, d)}) ⊔ edge a d) ⊔
            edge c b).Adj u v) at huv
          rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj] at huv
          rcases huv with (hK | had) | hcb
          · exact hxu.trans (Adj.reachable ((SimpleGraph.deleteEdges_le _) hK))
          · rw [SimpleGraph.edge_adj] at had
            rcases had.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact False.elim (hxa hxu)
            · exact False.elim (hxc (hxu.trans hcd.symm.reachable))
          · rw [SimpleGraph.edge_adj] at hcb
            rcases hcb.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact False.elim (hxc hxu)
            · exact False.elim (hxa (hxu.trans hab.symm.reachable))
        exact ih hxv
  · intro hxy
    obtain ⟨p⟩ := hxy
    suffices hwalk : forall {u v : V}, G.Walk u v ->
        G.Reachable x u ->
        (medialTwoEdgeSwitch G a b c d).Reachable x u ->
        (medialTwoEdgeSwitch G a b c d).Reachable x v by
      exact hwalk p (Reachable.refl _) (Reachable.refl _)
    intro u v p
    induction p with
    | nil => exact fun _ h => h
    | @cons u v w huv p ih =>
        intro hxu hswitchu
        have habuv : s(u, v) ≠ s(a, b) := by
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxa hxu
          · exact hxa (hxu.trans hab.symm.reachable)
        have hcduv : s(u, v) ≠ s(c, d) := by
          intro heq
          rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hxc hxu
          · exact hxc (hxu.trans hcd.symm.reachable)
        have hK : (G.deleteEdges {s(a, b), s(c, d)}).Adj u v := by
          rw [SimpleGraph.deleteEdges_adj]
          exact ⟨huv, by simp [habuv, hcduv]⟩
        have hswitchv : (medialTwoEdgeSwitch G a b c d).Reachable x v :=
          hswitchu.trans (Adj.reachable ((Or.inl (Or.inl hK) :
            (medialTwoEdgeSwitch G a b c d).Adj u v)))
        exact ih (hxu.trans huv.reachable) hswitchv

end

end StatMech.Universality
