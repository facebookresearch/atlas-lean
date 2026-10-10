/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.SetTheory.Cardinal.Finite
public import Batteries.Data.UnionFind.Lemmas
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Connected components using the canonical union-find

CLRS fourth edition, section 19.1, printed pages 522–523. This executes
CONNECTED-COMPONENTS with canonical Batteries UnionFind, union by rank and
path compression. Edges retain their input order, loops and duplicates.

The direct CSLib TimeM annotation counts MAKE-SET, FIND-SET and UNION calls:
(n, 2 * edges.length, n - number of graph components). A checked query performs
two FIND-SET calls and its carried store is retained even when UNION is skipped.
These are source call counts, not parent-visit, alpha, RAM, bit or space bounds.
-/

open Batteries Cslib.Algorithms.Lean

set_option autoImplicit false
namespace SimpleGraph

private theorem reachable_sup_edge_spec {V : Type*} (G : SimpleGraph V)
    (x y a b : V) :
    (G ⊔ SimpleGraph.edge x y).Reachable a b ↔
      G.Reachable a b ∨
        (G.Reachable a x ∧ G.Reachable y b) ∨
        (G.Reachable a y ∧ G.Reachable x b) := by
  constructor
  · intro hab
    rw [reachable_iff_reflTransGen] at hab
    induction hab with
    | refl =>
      exact Or.inl .rfl
    | tail h hadj ih =>
      rw [sup_adj] at hadj
      rcases hadj with hadj | hadj
      · rcases ih with hG | hxy | hyx
        · exact Or.inl (hG.trans hadj.reachable)
        · exact Or.inr (Or.inl ⟨hxy.1, hxy.2.trans hadj.reachable⟩)
        · exact Or.inr (Or.inr ⟨hyx.1, hyx.2.trans hadj.reachable⟩)
      · rw [edge_adj] at hadj
        rcases hadj.1 with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rcases ih with hG | hxy | hyx
          · exact Or.inr (Or.inl ⟨hG, .rfl⟩)
          · exact Or.inr (Or.inl ⟨hxy.1, .rfl⟩)
          · exact Or.inl hyx.1
        · rcases ih with hG | hxy | hyx
          · exact Or.inr (Or.inr ⟨hG, .rfl⟩)
          · exact Or.inl hxy.1
          · exact Or.inr (Or.inr ⟨hyx.1, .rfl⟩)
  · intro hab
    have hle : G ≤ G ⊔ SimpleGraph.edge x y := le_sup_left
    have hxy : (G ⊔ SimpleGraph.edge x y).Reachable x y := by
      by_cases h : x = y
      · subst y
        exact .rfl
      · apply Adj.reachable
        rw [sup_adj]
        exact Or.inr ((edge_adj x y x y).2 ⟨Or.inl ⟨rfl, rfl⟩, h⟩)
    rcases hab with hG | hcross | hcross
    · exact hG.mono hle
    · exact (hcross.1.mono hle).trans (hxy.trans (hcross.2.mono hle))
    · exact (hcross.1.mono hle).trans (hxy.symm.trans (hcross.2.mono hle))

private theorem card_components_sup_edge {V : Type*} [Finite V]
    (G : SimpleGraph V) (x y : V) (hxy : ¬ G.Reachable x y) :
    Nat.card (G ⊔ SimpleGraph.edge x y).ConnectedComponent + 1 =
      Nat.card G.ConnectedComponent := by
  classical
  let G' := G ⊔ SimpleGraph.edge x y
  let cy := G.connectedComponentMk y
  let cx := G.connectedComponentMk x
  let remaining := {c : G.ConnectedComponent // c ≠ cy}
  let componentMap : G.ConnectedComponent → G'.ConnectedComponent :=
    ConnectedComponent.map (Hom.ofLE (show G ≤ G' from le_sup_left))
  let restrictedMap : remaining → G'.ConnectedComponent :=
    fun c => componentMap c.1
  have hcx : cx ≠ cy := by
    intro h
    exact hxy (ConnectedComponent.exact h)
  have hmap_injective :
      ∀ c d : G.ConnectedComponent,
        c ≠ cy → d ≠ cy → componentMap c = componentMap d → c = d := by
    refine ConnectedComponent.ind₂ ?_
    intro a b ha hb hab
    have hab' : G'.Reachable a b := by
      apply ConnectedComponent.exact
      simpa [componentMap] using hab
    change (G ⊔ SimpleGraph.edge x y).Reachable a b at hab'
    rcases (reachable_sup_edge_spec G x y a b).1 hab' with h | h | h
    · exact ConnectedComponent.sound h
    · exact (hb (ConnectedComponent.sound h.2).symm).elim
    · exact (ha (ConnectedComponent.sound h.1)).elim
  have hrestricted_injective : Function.Injective restrictedMap := by
    intro c d h
    apply Subtype.ext
    exact hmap_injective c.1 d.1 c.2 d.2 h
  have hmerged : componentMap cx = componentMap cy := by
    apply ConnectedComponent.sound
    change (G ⊔ SimpleGraph.edge x y).Reachable x y
    exact (reachable_sup_edge_spec G x y x y).2
      (Or.inr (Or.inl ⟨.rfl, .rfl⟩))
  have hrestricted_surjective : Function.Surjective restrictedMap := by
    intro c
    rcases ConnectedComponent.surjective_map_ofLE
        (show G ≤ G' from le_sup_left) c with ⟨d, hd⟩
    by_cases hdy : d = cy
    · refine ⟨⟨cx, hcx⟩, ?_⟩
      change componentMap cx = c
      calc
        componentMap cx = componentMap cy := hmerged
        _ = componentMap d := congrArg componentMap hdy.symm
        _ = c := hd
    · refine ⟨⟨d, hdy⟩, ?_⟩
      exact hd
  let componentEquiv : remaining ≃ G'.ConnectedComponent :=
    Equiv.ofBijective restrictedMap
      ⟨hrestricted_injective, hrestricted_surjective⟩
  let := Fintype.ofFinite G.ConnectedComponent
  let := Fintype.ofFinite G'.ConnectedComponent
  let := Fintype.ofFinite remaining
  let onlyY := {c : G.ConnectedComponent // c = cy}
  let onlyYEquiv : onlyY ≃ PUnit.{1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨cy, rfl⟩
      left_inv := by
        intro c
        apply Subtype.ext
        exact c.2.symm
      right_inv := by
        intro u
        cases u
        rfl }
  have honlyY : Fintype.card onlyY = 1 := by
    exact Fintype.card_congr onlyYEquiv
  have hremaining :
      Fintype.card remaining = Fintype.card G.ConnectedComponent - 1 := by
    have h := Fintype.card_subtype_compl
      (fun c : G.ConnectedComponent => c = cy)
    change Fintype.card remaining =
      Fintype.card G.ConnectedComponent - Fintype.card onlyY at h
    simpa [honlyY] using h
  have hcard :
      Fintype.card G'.ConnectedComponent + 1 =
        Fintype.card G.ConnectedComponent := by
    calc
      Fintype.card G'.ConnectedComponent + 1 =
          Fintype.card remaining + 1 := by
        rw [Fintype.card_congr componentEquiv]
      _ = (Fintype.card G.ConnectedComponent - 1) + 1 := by
        rw [hremaining]
      _ = Fintype.card G.ConnectedComponent := by
        apply Nat.sub_add_cancel
        exact Fintype.card_pos_iff.mpr ⟨cy⟩
  change Nat.card G'.ConnectedComponent + 1 = Nat.card G.ConnectedComponent
  simpa only [Nat.card_eq_fintype_card] using hcard

end SimpleGraph
namespace Batteries.UnionFind

private theorem fin_val_transport {n m : Nat} (h : m = n) (i : Fin n) :
    (h ▸ i : Fin m).val = i.val := by
  cases h
  rfl

/-- The canonical checked query preserves size and the complete equivalence relation. -/
public theorem checkEquiv_spec :
  ∀ (uf : UnionFind) (x y : Fin uf.size),
    (uf.checkEquiv x y).1.size = uf.size ∧
    ((uf.checkEquiv x y).2 = true ↔ UnionFind.Equiv uf x.val y.val) ∧
    ∀ (a b : Nat), UnionFind.Equiv (uf.checkEquiv x y).1 a b ↔ UnionFind.Equiv uf a b := by
  intro uf x y
  unfold checkEquiv
  split
  rename_i _ s₁ r₁ _ hs₁ h₁
  split
  rename_i _ s₂ r₂ _ hs₂ h₂
  have root₁ : r₁ = uf.rootD x.val := by
    have h := find_root_2 uf x
    rw [h₁] at h
    exact h
  have root₂ : r₂ = s₁.rootD y.val := by
    have h := find_root_2 s₁ (hs₁ ▸ y)
    rw [h₂] at h
    exact h.trans (congrArg s₁.rootD (fin_val_transport hs₁ y))
  have unchanged₁ := fun a ↦ find_root_1 uf x a
  have unchanged₂ := fun a ↦ find_root_1 s₁ (hs₁ ▸ y) a
  simp_all [UnionFind.Equiv]

end Batteries.UnionFind
namespace Batteries.UnionFind

private theorem checkSize (uf : UnionFind) (x y : Fin uf.size) :
    (uf.checkEquiv x y).1.size = uf.size := by
  unfold UnionFind.checkEquiv
  split
  split
  simp_all

private theorem unionSize (uf : UnionFind) (x y : Fin uf.size) :
    (uf.union x y).size = uf.size := by
  unfold UnionFind.union
  split
  dsimp only
  simp_all [UnionFind.size, UnionFind.link, UnionFind.linkAux_size]

private theorem merge_of_equiv (self : UnionFind) (x y : Nat)
    (hxy : UnionFind.Equiv self x y) (a b : Nat) :
    UnionFind.Equiv self a b ↔
      UnionFind.Equiv self a b ∨
        (UnionFind.Equiv self a x ∧ UnionFind.Equiv self y b) ∨
        (UnionFind.Equiv self a y ∧ UnionFind.Equiv self x b) := by
  constructor
  · exact Or.inl
  · rintro (h | ⟨hax, hyb⟩ | ⟨hay, hxb⟩)
    · exact h
    · exact hax.trans (hxy.trans hyb)
    · exact hay.trans (hxy.symm.trans hxb)

private def processEdge (n : Nat) (state : {s : UnionFind // s.size = n})
    (edge : Fin n × Fin n) : TimeM (Nat × Nat × Nat) {s : UnionFind // s.size = n} :=
  (fun state edge ↦ do
    TimeM.tick (0, 2, 0)
    let x := Fin.cast state.property.symm edge.1
    let y := Fin.cast state.property.symm edge.2
    let checked := state.val.checkEquiv x y
    have hc : checked.1.size = n := (checkSize state.val x y).trans state.property
    if checked.2 then
      pure ⟨checked.1, hc⟩
    else
      TimeM.tick (0, 0, 1)
      let x' := Fin.cast hc.symm edge.1
      let y' := Fin.cast hc.symm edge.2
      pure ⟨checked.1.union x' y', (unionSize checked.1 x' y').trans hc⟩) state edge

private theorem processEdge_equiv (n : Nat) (state : {s : UnionFind // s.size = n})
    (edge : Fin n × Fin n) (a b : Nat) :
    UnionFind.Equiv (processEdge n state edge).ret.val a b ↔
      UnionFind.Equiv state.val a b ∨
        (UnionFind.Equiv state.val a edge.1.val ∧ UnionFind.Equiv state.val edge.2.val b) ∨
        (UnionFind.Equiv state.val a edge.2.val ∧ UnionFind.Equiv state.val edge.1.val b) := by
  have hspec := Batteries.UnionFind.checkEquiv_spec state.val
    (Fin.cast state.property.symm edge.1) (Fin.cast state.property.symm edge.2)
  unfold processEdge
  simp only [TimeM.ret_bind]
  split
  · rename_i h
    simp only [TimeM.ret_pure]
    rw [hspec.2.2]
    apply merge_of_equiv
    simpa only [Fin.val_cast] using hspec.2.1.mp h
  · simp only [TimeM.ret_bind, TimeM.ret_pure]
    rw [UnionFind.equiv_union]
    simp only [hspec.2.2, Fin.val_cast]

private theorem fromEdgeSet_cons {V : Type*} (p : V × V) (edges : List (V × V)) :
    SimpleGraph.fromEdgeSet {e | e ∈ (p :: edges).map (fun q ↦ s(q.1, q.2))} =
      SimpleGraph.edge p.1 p.2 ⊔
        SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun q ↦ s(q.1, q.2))} := by
  have h : {e | e ∈ (p :: edges).map (fun q ↦ s(q.1, q.2))} =
      {s(p.1, p.2)} ∪ {e | e ∈ edges.map (fun q ↦ s(q.1, q.2))} := by
    ext e
    simp
  rw [h, SimpleGraph.fromEdgeSet_union]
  rfl

private theorem processEdge_reachable (n : Nat) (state : {s : UnionFind // s.size = n})
    (G : SimpleGraph (Fin n))
    (hpart : ∀ a b : Fin n, UnionFind.Equiv state.val a.val b.val ↔ G.Reachable a b)
    (edge : Fin n × Fin n) (a b : Fin n) :
    UnionFind.Equiv (processEdge n state edge).ret.val a.val b.val ↔
      (G ⊔ SimpleGraph.edge edge.1 edge.2).Reachable a b := by
  rw [processEdge_equiv, SimpleGraph.reachable_sup_edge_spec]
  simp only [hpart]

private theorem foldEdges_reachable (n : Nat) (edges : List (Fin n × Fin n))
    (state : {s : UnionFind // s.size = n}) (G : SimpleGraph (Fin n))
    (hpart : ∀ a b : Fin n, UnionFind.Equiv state.val a.val b.val ↔ G.Reachable a b)
    (a b : Fin n) :
    UnionFind.Equiv (edges.foldlM (processEdge n) state).ret.val a.val b.val ↔
      (G ⊔ SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun q ↦ s(q.1, q.2))}).Reachable
        a b := by
  induction edges generalizing state G with
  | nil => simpa [List.foldlM] using hpart a b
  | cons edge edges ih =>
    simp only [List.foldlM, TimeM.ret_bind]
    have hs := fun u v ↦ processEdge_reachable n state G hpart edge u v
    simpa only [fromEdgeSet_cons, sup_assoc] using
      ih (processEdge n state edge).ret (G ⊔ SimpleGraph.edge edge.1 edge.2) hs

private def allocateVertices : (n : Nat) → TimeM (Nat × Nat × Nat) {s : UnionFind // s.size = n}
  | 0 => pure ⟨UnionFind.empty, rfl⟩
  | n + 1 => do
    let s ← allocateVertices n
    TimeM.tick (1, 0, 0)
    pure ⟨s.val.push, by
      have h : s.val.push.size = s.val.size + 1 := by
        simp only [UnionFind.size, UnionFind.arr_push, Array.size_push]
      exact h.trans (congrArg (fun x ↦ x + 1) s.property)⟩

/-- Run CLRS CONNECTED-COMPONENTS in input order, retaining query compression on both branches. -/
public def connectedComponents (n : Nat) (edges : List (Fin n × Fin n)) :
    TimeM (Nat × Nat × Nat) {s : UnionFind // s.size = n} := do
  let initial ← allocateVertices n
  edges.foldlM (fun state edge ↦ do
    TimeM.tick (0, 2, 0)
    let x := Fin.cast state.property.symm edge.1
    let y := Fin.cast state.property.symm edge.2
    let checked := state.val.checkEquiv x y
    have hc : checked.1.size = n := (checkSize state.val x y).trans state.property
    if checked.2 then
      pure ⟨checked.1, hc⟩
    else
      TimeM.tick (0, 0, 1)
      let x' := Fin.cast hc.symm edge.1
      let y' := Fin.cast hc.symm edge.2
      pure ⟨checked.1.union x' y', (unionSize checked.1 x' y').trans hc⟩) initial

private theorem allocateVertices_rootD (n i : Nat) :
    (allocateVertices n).ret.val.rootD i = i := by
  induction n with
  | zero => simp [allocateVertices]
  | succ n ih => simpa [allocateVertices] using ih

private theorem allocateVertices_time (n : Nat) :
    (allocateVertices n).time = (n, 0, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [allocateVertices, ih]

/-- The returned union-find has exactly the requested number of allocated vertices. -/
public theorem connectedComponents_size (n : Nat) (edges : List (Fin n × Fin n)) :
    (connectedComponents n edges).ret.val.size = n :=
  (connectedComponents n edges).ret.property

/-- The returned canonical partition is exactly undirected graph reachability. -/
public theorem connectedComponents_equiv_iff_reachable (n : Nat)
    (edges : List (Fin n × Fin n)) (a b : Fin n) :
    UnionFind.Equiv (connectedComponents n edges).ret.val a.val b.val ↔
      (SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun q ↦ s(q.1, q.2))}).Reachable a b := by
  have initial : ∀ u v : Fin n,
      UnionFind.Equiv (allocateVertices n).ret.val u.val v.val ↔
        (⊥ : SimpleGraph (Fin n)).Reachable u v := by
    intro u v
    simp [UnionFind.Equiv, allocateVertices_rootD, SimpleGraph.reachable_bot, Fin.val_inj]
  unfold connectedComponents
  simp only [TimeM.ret_bind]
  change UnionFind.Equiv
    (edges.foldlM (processEdge n) (allocateVertices n).ret).ret.val a.val b.val ↔ _
  simpa only [bot_sup_eq] using
    foldEdges_reachable n edges (allocateVertices n).ret ⊥ initial a b

private theorem processEdge_time (n : Nat)
    (state : {s : UnionFind // s.size = n}) (edge : Fin n × Fin n) :
    let x := Fin.cast state.property.symm edge.1
    let y := Fin.cast state.property.symm edge.2
    (processEdge n state edge).time =
      (0, 2, if (state.val.checkEquiv x y).2 then 0 else 1) := by
  unfold processEdge
  simp only [TimeM.time_bind]
  split <;> simp_all

private theorem card_components_sup_edge_of_reachable {V : Type*} [Finite V]
    (G : SimpleGraph V) (x y : V) (hxy : G.Reachable x y) :
    Nat.card (G ⊔ SimpleGraph.edge x y).ConnectedComponent =
      Nat.card G.ConnectedComponent := by
  let componentMap : G.ConnectedComponent →
      (G ⊔ SimpleGraph.edge x y).ConnectedComponent :=
    SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE le_sup_left)
  have hinj : Function.Injective componentMap := by
    refine SimpleGraph.ConnectedComponent.ind₂ ?_
    intro a b hab
    have hab' : (G ⊔ SimpleGraph.edge x y).Reachable a b := by
      apply SimpleGraph.ConnectedComponent.exact
      exact hab
    apply SimpleGraph.ConnectedComponent.sound
    rcases (SimpleGraph.reachable_sup_edge_spec G x y a b).1 hab' with h | h | h
    · exact h
    · exact h.1.trans (hxy.trans h.2)
    · exact h.1.trans (hxy.symm.trans h.2)
  exact (Nat.card_eq_of_bijective componentMap
    ⟨hinj, SimpleGraph.ConnectedComponent.surjective_map_ofLE le_sup_left⟩).symm

private theorem processEdge_time_card (n : Nat)
    (state : {s : UnionFind // s.size = n}) (G : SimpleGraph (Fin n))
    (hpart : ∀ a b : Fin n, UnionFind.Equiv state.val a.val b.val ↔ G.Reachable a b)
    (edge : Fin n × Fin n) :
    Nat.card (G ⊔ SimpleGraph.edge edge.1 edge.2).ConnectedComponent +
      (processEdge n state edge).time.2.2 = Nat.card G.ConnectedComponent := by
  let x := Fin.cast state.property.symm edge.1
  let y := Fin.cast state.property.symm edge.2
  have hguard : (state.val.checkEquiv x y).2 = true ↔ G.Reachable edge.1 edge.2 := by
    simpa only [x, y, Fin.val_cast] using
      (Batteries.UnionFind.checkEquiv_spec state.val x y).2.1.trans (hpart edge.1 edge.2)
  rw [processEdge_time]
  dsimp only
  split
  · rename_i h
    simpa only [Nat.add_zero] using
      card_components_sup_edge_of_reachable G edge.1 edge.2 (hguard.mp h)
  · rename_i h
    exact SimpleGraph.card_components_sup_edge G edge.1 edge.2
      (fun hr ↦ h (hguard.mpr hr))

private theorem foldEdges_time_card (n : Nat) (edges : List (Fin n × Fin n))
    (state : {s : UnionFind // s.size = n}) (G : SimpleGraph (Fin n))
    (hpart : ∀ a b : Fin n, UnionFind.Equiv state.val a.val b.val ↔ G.Reachable a b) :
    let graph := G ⊔
      SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun q ↦ s(q.1, q.2))}
    let actual := edges.foldlM (processEdge n) state
    actual.time.1 = 0 ∧ actual.time.2.1 = 2 * edges.length ∧
      Nat.card graph.ConnectedComponent + actual.time.2.2 =
        Nat.card G.ConnectedComponent := by
  induction edges generalizing state G with
  | nil => simp [List.foldlM]
  | cons edge edges ih =>
    have hs := fun u v ↦ processEdge_reachable n state G hpart edge u v
    have hi := ih (processEdge n state edge).ret (G ⊔ SimpleGraph.edge edge.1 edge.2) hs
    have hc := processEdge_time_card n state G hpart edge
    have ht := processEdge_time n state edge
    dsimp only at hi ⊢
    simp only [List.foldlM, TimeM.time_bind, Prod.fst_add, Prod.snd_add,
      List.length_cons, fromEdgeSet_cons, ← sup_assoc]
    have h0 : (processEdge n state edge).time.1 = 0 := by
      exact congrArg Prod.fst ht
    have h1 : (processEdge n state edge).time.2.1 = 2 := by
      exact congrArg (fun t : Nat × Nat × Nat ↦ t.2.1) ht
    rcases hi with ⟨hi0, hi1, hi2⟩
    constructor
    · omega
    · constructor
      · omega
      · omega

private theorem card_components_bot_fin (n : Nat) :
    Nat.card (⊥ : SimpleGraph (Fin n)).ConnectedComponent = n := by
  have hb : Function.Bijective (⊥ : SimpleGraph (Fin n)).connectedComponentMk := by
    constructor
    · intro u v h
      exact SimpleGraph.reachable_bot.mp (SimpleGraph.ConnectedComponent.exact h)
    · exact Quot.mk_surjective
  calc
    Nat.card (⊥ : SimpleGraph (Fin n)).ConnectedComponent = Nat.card (Fin n) :=
      (Nat.card_eq_of_bijective _ hb).symm
    _ = n := Nat.card_fin n

/-- Actual MAKE-SET, FIND-SET and conditional UNION call counts, with conservation. -/
public theorem connectedComponents_time_spec :
  ∀ (n : Nat) (edges : List (Fin n × Fin n)),
    let graph : SimpleGraph (Fin n) :=
      SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun p ↦ s(p.1, p.2))}
    (connectedComponents n edges).time =
      (n, 2 * edges.length, n - Nat.card graph.ConnectedComponent) ∧
    Nat.card graph.ConnectedComponent + (connectedComponents n edges).time.2.2 = n ∧
    (0 < n → (connectedComponents n edges).time.2.2 ≤ n - 1) := by
  intro n edges
  dsimp only
  have initial : ∀ u v : Fin n,
      UnionFind.Equiv (allocateVertices n).ret.val u.val v.val ↔
        (⊥ : SimpleGraph (Fin n)).Reachable u v := by
    intro u v
    simp [UnionFind.Equiv, allocateVertices_rootD, SimpleGraph.reachable_bot, Fin.val_inj]
  have hf := foldEdges_time_card n edges (allocateVertices n).ret ⊥ initial
  dsimp only at hf
  simp only [bot_sup_eq, card_components_bot_fin] at hf
  have ht : (connectedComponents n edges).time = (allocateVertices n).time +
      (edges.foldlM (processEdge n) (allocateVertices n).ret).time := rfl
  have h0 : (connectedComponents n edges).time.1 = n := by
    simpa only [allocateVertices_time, Prod.fst_add, hf.1, Nat.add_zero] using
      congrArg Prod.fst ht
  have h1 : (connectedComponents n edges).time.2.1 = 2 * edges.length := by
    simpa only [allocateVertices_time, Prod.snd_add, Prod.fst_add, hf.2.1,
      Nat.zero_add] using congrArg (fun t : Nat × Nat × Nat ↦ t.2.1) ht
  have h2 : (connectedComponents n edges).time.2.2 =
      (edges.foldlM (processEdge n) (allocateVertices n).ret).time.2.2 := by
    simpa only [allocateVertices_time, Prod.snd_add, Nat.zero_add] using
      congrArg (fun t : Nat × Nat × Nat ↦ t.2.2) ht
  have hc : Nat.card (SimpleGraph.fromEdgeSet
      {e | e ∈ edges.map (fun p ↦ s(p.1, p.2))}).ConnectedComponent +
      (connectedComponents n edges).time.2.2 = n := by
    rw [h2]
    exact hf.2.2
  refine ⟨?_, hc, ?_⟩
  · apply Prod.ext h0
    apply Prod.ext h1
    change (connectedComponents n edges).time.2.2 = n - Nat.card
      (SimpleGraph.fromEdgeSet {e | e ∈ edges.map (fun p ↦ s(p.1, p.2))}).ConnectedComponent
    omega
  · intro hn
    let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hp := Nat.card_pos (α := (SimpleGraph.fromEdgeSet
      {e | e ∈ edges.map (fun p ↦ s(p.1, p.2))}).ConnectedComponent)
    omega

end Batteries.UnionFind
