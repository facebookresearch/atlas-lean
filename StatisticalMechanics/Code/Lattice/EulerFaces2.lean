/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Lattice.Cyclomatic

open SimpleGraph Set



set_option linter.unusedSectionVars false

namespace StatMech.Lattice

variable {V : Type*}








theorem reachable_sup_edge (G : SimpleGraph V) (a b x y : V) :
    (G ⊔ edge a b).Reachable x y ↔
      G.Reachable x y ∨ (G.Reachable x a ∧ G.Reachable b y) ∨
        (G.Reachable x b ∧ G.Reachable a y) := by
  constructor
  · rintro ⟨w⟩
    induction w with
    | nil => exact Or.inl (Reachable.refl _)
    | @cons u v z huv w ih =>
      rcases ih with hg | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [sup_adj] at huv
        rcases huv with hguv | hed
        · exact Or.inl ((hguv.reachable).trans hg)
        · rw [edge_adj] at hed
          obtain ⟨huv2, _⟩ := hed
          rcases huv2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inr (Or.inl ⟨Reachable.refl _, hg⟩)
          · exact Or.inr (Or.inr ⟨Reachable.refl _, hg⟩)
      · rw [sup_adj] at huv
        rcases huv with hguv | hed
        · exact Or.inr (Or.inl ⟨(hguv.reachable).trans h1, h2⟩)
        · rw [edge_adj] at hed
          obtain ⟨huv2, _⟩ := hed
          rcases huv2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl (h1.symm.trans h2)
          · exact Or.inl h2
      · rw [sup_adj] at huv
        rcases huv with hguv | hed
        · exact Or.inr (Or.inr ⟨(hguv.reachable).trans h1, h2⟩)
        · rw [edge_adj] at hed
          obtain ⟨huv2, _⟩ := hed
          rcases huv2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl h2
          · exact Or.inl (h1.symm.trans h2)
  · have hle : G ≤ G ⊔ edge a b := le_sup_left
    have hab : (G ⊔ edge a b).Reachable a b := by
      by_cases h : a = b
      · subst h; exact Reachable.refl _
      · exact Adj.reachable (by rw [sup_adj]; right; rw [edge_adj]; exact ⟨Or.inl ⟨rfl, rfl⟩, h⟩)
    rintro (hg | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hg.mono hle
    · exact (h1.mono hle).trans (hab.trans (h2.mono hle))
    · exact (h1.mono hle).trans (hab.symm.trans (h2.mono hle))





theorem card_subtype_ne_add_one {α : Type*} [Finite α] (a : α) :
    Nat.card {x : α // x ≠ a} + 1 = Nat.card α := by
  classical
  have : Fintype α := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]
  have hpos : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  omega



variable [Finite V] [DecidableEq V]





theorem card_components_sup_edge_of_reachable (G : SimpleGraph V) (a b : V)
    (hab : G.Reachable a b) :
    Nat.card (G ⊔ edge a b).ConnectedComponent = Nat.card G.ConnectedComponent := by
  classical
  have hinj : Function.Injective
      (ConnectedComponent.map (Hom.ofLE (le_sup_left : G ≤ G ⊔ edge a b))) := by
    intro c c'
    refine ConnectedComponent.ind₂ ?_ c c'
    intro x y h
    simp only [ConnectedComponent.map_mk] at h
    rw [ConnectedComponent.eq] at h ⊢
    have h' : (G ⊔ edge a b).Reachable x y := h
    rw [reachable_sup_edge] at h'
    rcases h' with hg | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hg
    · exact h1.trans (hab.trans h2)
    · exact h1.trans (hab.symm.trans h2)
  have hsurj := ConnectedComponent.surjective_map_ofLE (le_sup_left : G ≤ G ⊔ edge a b)
  exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm




theorem card_components_sup_edge_of_not_reachable (G : SimpleGraph V) (a b : V)
    (hab : ¬ G.Reachable a b) :
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
    show (G ⊔ edge a b).connectedComponentMk _ = (G ⊔ edge a b).connectedComponentMk _ ↔ _
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
    · exact ⟨⟨ca, hane⟩, by show f ca = d; rw [hfeq]; exact hccb ▸ hc⟩
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






theorem deleteEdges_sup_edge_eq (G : SimpleGraph V) (a b : V) (he : s(a, b) ∈ G.edgeSet) :
    G = (G.deleteEdges {s(a, b)}) ⊔ edge a b := by
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at he
  ext x y
  simp only [sup_adj, deleteEdges_adj, edge_adj, Set.mem_singleton_iff]
  constructor
  · intro hxy
    by_cases hc : s(x, y) = s(a, b)
    · right
      rw [Sym2.eq_iff] at hc
      have hne : x ≠ y := G.ne_of_adj hxy
      rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Or.inl ⟨rfl, rfl⟩, hne⟩
      · exact ⟨Or.inr ⟨rfl, rfl⟩, hne⟩
    · exact Or.inl ⟨hxy, hc⟩
  · rintro (⟨h, _⟩ | ⟨hc, _⟩)
    · exact h
    · rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj
      · exact hadj.symm


theorem card_edgeSet_deleteEdges_add_one (G : SimpleGraph V) (a b : V)
    (he : s(a, b) ∈ G.edgeSet) :
    (G.deleteEdges {s(a, b)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_diff_singleton_add_one he (Set.toFinite _)



theorem card_edgeSet_sup_edge (G : SimpleGraph V) {a b : V} (hne : a ≠ b)
    (hadj : ¬ G.Adj a b) :
    (G ⊔ edge a b).edgeSet.ncard = G.edgeSet.ncard + 1 := by
  have hsub : (G ⊔ edge a b).edgeSet = insert s(a, b) G.edgeSet := by
    ext e
    simp only [edgeSet_sup, edge, edgeSet_fromEdgeSet, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff, Set.mem_insert_iff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact Or.inr h
      · exact Or.inl h
    · rintro (rfl | h)
      · refine Or.inr ⟨rfl, ?_⟩
        rw [Sym2.mem_diagSet, Sym2.mk_isDiag_iff]; exact hne
      · exact Or.inl h
  rw [hsub, Set.ncard_insert_of_notMem (by rw [SimpleGraph.mem_edgeSet]; exact hadj)
    (Set.toFinite _)]


theorem card_components_bot :
    Nat.card (⊥ : SimpleGraph V).ConnectedComponent = Nat.card V := by
  classical
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (⊥ : SimpleGraph V).connectedComponentMk ⟨?_, ?_⟩
  · intro x y h
    rw [ConnectedComponent.eq, reachable_bot] at h; exact h
  · intro c; refine ConnectedComponent.ind ?_ c; intro v; exact ⟨v, rfl⟩













theorem card_le_edgeSet_add_components (G : SimpleGraph V) :
    Nat.card V ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  classical
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite G.edgeSet)).mp hn
      have hbot : G = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot; rw [card_components_bot]; simp
    · have hne : G.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      set G' := G.deleteEdges {s(a, b)} with hG'
      have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
      have hdrop : G'.edgeSet.ncard + 1 = G.edgeSet.ncard := card_edgeSet_deleteEdges_add_one G a b he
      have hn' : G'.edgeSet.ncard = n - 1 := by omega
      have ihG' : Nat.card V ≤ G'.edgeSet.ncard + Nat.card G'.ConnectedComponent := by
        have := ih (n - 1) (by omega) G' hn'; rwa [hn']
      by_cases hr : G'.Reachable a b
      · have hc := card_components_sup_edge_of_reachable G' a b hr
        rw [hGeq] at hdrop ⊢; rw [hc]; omega
      · have hc := card_components_sup_edge_of_not_reachable G' a b hr
        rw [hGeq] at hdrop ⊢; omega






noncomputable def nullity (G : SimpleGraph V) : ℕ :=
  (G.edgeSet.ncard + Nat.card G.ConnectedComponent) - Nat.card V





noncomputable def faceCount (G : SimpleGraph V) : ℕ := nullity G + 1



theorem faceCount_sup_edge_of_reachable (G : SimpleGraph V) {a b : V} (hne : a ≠ b)
    (hadj : ¬ G.Adj a b) (hab : G.Reachable a b) :
    faceCount (G ⊔ edge a b) = faceCount G + 1 := by
  have hbound := card_le_edgeSet_add_components G
  have hedge := card_edgeSet_sup_edge G hne hadj
  have hcomp := card_components_sup_edge_of_reachable G a b hab
  unfold faceCount nullity
  rw [hedge, hcomp]
  omega




theorem faceCount_sup_edge_of_not_reachable (G : SimpleGraph V) {a b : V} (hne : a ≠ b)
    (hadj : ¬ G.Adj a b) (hab : ¬ G.Reachable a b) :
    faceCount (G ⊔ edge a b) = faceCount G := by
  have hbound := card_le_edgeSet_add_components G
  have hedge := card_edgeSet_sup_edge G hne hadj
  have hcomp := card_components_sup_edge_of_not_reachable G a b hab
  unfold faceCount nullity
  rw [hedge]
  omega












theorem euler_relation (G : SimpleGraph V) :
    Nat.card V + faceCount G = G.edgeSet.ncard + Nat.card G.ConnectedComponent + 1 := by
  have hbound := card_le_edgeSet_add_components G
  unfold faceCount nullity
  omega



theorem euler_relation_sub (G : SimpleGraph V) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = Nat.card G.ConnectedComponent + 1 := by
  have h := euler_relation G
  have : (Nat.card V : ℤ) + (faceCount G : ℤ)
      = (G.edgeSet.ncard : ℤ) + (Nat.card G.ConnectedComponent : ℤ) + 1 := by exact_mod_cast h
  linarith




theorem card_components_eq_one_of_connected {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card G.ConnectedComponent = 1 := by
  haveI : Nonempty V := hG.nonempty
  haveI := hG.preconnected.subsingleton_connectedComponent
  haveI : Nonempty G.ConnectedComponent := ⟨G.connectedComponentMk (Classical.arbitrary V)⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨inferInstance, inferInstance⟩



theorem euler_connected_nat {G : SimpleGraph V} (hG : G.Connected) :
    Nat.card V + faceCount G = G.edgeSet.ncard + 2 := by
  have h := euler_relation G
  rw [card_components_eq_one_of_connected hG] at h
  omega



theorem euler_connected {G : SimpleGraph V} (hG : G.Connected) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 := by
  have h := euler_relation_sub G
  rw [card_components_eq_one_of_connected hG] at h
  push_cast at h ⊢
  linarith






theorem nullity_eq_zero_of_isAcyclic {G : SimpleGraph V} (hG : G.IsAcyclic) :
    nullity G = 0 := by
  classical
  
  
  
  revert hG
  generalize hn : G.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
    intro hG
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · subst hz
      have hempty : G.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite G.edgeSet)).mp hn
      have hbot : G = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      unfold nullity
      rw [hn, card_components_bot]; simp
    · have hne : G.edgeSet.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite _), hn]; exact hpos
      obtain ⟨e, he⟩ := hne
      obtain ⟨a, b⟩ := e
      set G' := G.deleteEdges {s(a, b)} with hG'
      have hGeq : G = G' ⊔ edge a b := deleteEdges_sup_edge_eq G a b he
      have hdrop : G'.edgeSet.ncard + 1 = G.edgeSet.ncard :=
        card_edgeSet_deleteEdges_add_one G a b he
      have hn' : G'.edgeSet.ncard = n - 1 := by omega
      have hacyc' : G'.IsAcyclic := hG.anti (deleteEdges_le _)
      
      have hbridge : G.IsBridge s(a, b) := (isAcyclic_iff_forall_edge_isBridge.mp hG) he
      have hnr : ¬ G'.Reachable a b := (isBridge_iff.mp hbridge).2
      have hne_ab : a ≠ b := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
      have hadj' : ¬ G'.Adj a b := by simp [hG', deleteEdges_adj]
      have ih' : nullity G' = 0 := ih (n - 1) (by omega) hn' hacyc'
      have hface : faceCount G = faceCount G' := by
        rw [hGeq]; exact faceCount_sup_edge_of_not_reachable G' hne_ab hadj' hnr
      unfold faceCount nullity at hface
      unfold nullity at ih' ⊢
      have hbound := card_le_edgeSet_add_components G
      have hbound' := card_le_edgeSet_add_components G'
      omega


theorem faceCount_eq_one_of_isAcyclic {G : SimpleGraph V} (hG : G.IsAcyclic) :
    faceCount G = 1 := by
  unfold faceCount; rw [nullity_eq_zero_of_isAcyclic hG]




theorem euler_tree {G : SimpleGraph V} (hG : G.IsTree) :
    (Nat.card V : ℤ) - G.edgeSet.ncard + faceCount G = 2 ∧ faceCount G = 1 := by
  refine ⟨euler_connected hG.connected, faceCount_eq_one_of_isAcyclic hG.isAcyclic⟩










theorem nullity_eq_cyclomaticNumber {G : SimpleGraph V} [Fintype V] [Fintype G.edgeSet]
    (hG : G.Connected) :
    nullity G = cyclomaticNumber G := by
  unfold nullity cyclomaticNumber
  rw [card_components_eq_one_of_connected hG, Nat.card_eq_fintype_card]
  congr 1
  rw [Set.ncard_eq_toFinset_card', edgeFinset]



theorem faceCount_eq_cyclomaticNumber_add_one {G : SimpleGraph V} [Fintype V]
    [Fintype G.edgeSet] (hG : G.Connected) :
    faceCount G = cyclomaticNumber G + 1 := by
  unfold faceCount; rw [nullity_eq_cyclomaticNumber hG]





















end StatMech.Lattice
