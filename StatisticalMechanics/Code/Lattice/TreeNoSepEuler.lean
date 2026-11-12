/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.EulerComponentCount
import Code.Lattice.EulerFaces

open SimpleGraph Set

set_option linter.unusedSectionVars false

namespace StatMech

namespace Lattice



variable {V : Type*} [Finite V] [DecidableEq V]





theorem tnse_connected_of_card_components_eq_one {G : SimpleGraph V}
    (hcard : Nat.card G.ConnectedComponent = 1) : G.Connected := by
  classical
  have hu := Nat.card_eq_one_iff_unique.mp hcard
  have hss : Subsingleton G.ConnectedComponent := hu.1
  obtain ⟨c⟩ := hu.2
  have hV : Nonempty V := c.exists_rep.elim fun v _ => ⟨v⟩
  rw [connected_iff]
  refine ⟨fun x y => ?_, hV⟩
  exact ConnectedComponent.exact (Subsingleton.elim (G.connectedComponentMk x)
    (G.connectedComponentMk y))





theorem tnse_connected_deleteEdge_of_nonbridge (A : SimpleGraph V) (hA : A.Connected) {a b : V}
    (he : s(a, b) ∈ A.edgeSet) (hr : (A.deleteEdges {s(a, b)}).Reachable a b) :
    (A.deleteEdges {s(a, b)}).Connected := by
  have hcard : Nat.card (A.deleteEdges {s(a, b)}).ConnectedComponent = 1 := by
    rw [ecc_deleteEdge_card_nonbridge A he hr, card_components_eq_one_of_connected hA]
  exact tnse_connected_of_card_components_eq_one hcard




def tnse_IsNonBridgeEdge (A : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∃ a b : V, e = s(a, b) ∧ s(a, b) ∈ A.edgeSet ∧ (A.deleteEdges {s(a, b)}).Reachable a b



theorem tnse_connected_deleteEdge_of_isNonBridge (A : SimpleGraph V) (hA : A.Connected)
    {e : Sym2 V} (he : tnse_IsNonBridgeEdge A e) : (A.deleteEdges {e}).Connected := by
  obtain ⟨a, b, rfl, hmem, hr⟩ := he
  exact tnse_connected_deleteEdge_of_nonbridge A hA hmem hr




def tnse_deleteList (A : SimpleGraph V) : List (Sym2 V) → SimpleGraph V
  | [] => A
  | e :: L => (tnse_deleteList A L).deleteEdges {e}

@[simp] theorem tnse_deleteList_nil (A : SimpleGraph V) : tnse_deleteList A [] = A := rfl

@[simp] theorem tnse_deleteList_cons (A : SimpleGraph V) (e : Sym2 V) (L : List (Sym2 V)) :
    tnse_deleteList A (e :: L) = (tnse_deleteList A L).deleteEdges {e} := rfl






def tnse_AllNonBridge (A : SimpleGraph V) : List (Sym2 V) → Prop
  | [] => True
  | e :: L => tnse_IsNonBridgeEdge (tnse_deleteList A L) e ∧ tnse_AllNonBridge A L

@[simp] theorem tnse_allNonBridge_nil (A : SimpleGraph V) : tnse_AllNonBridge A [] := trivial

theorem tnse_allNonBridge_cons {A : SimpleGraph V} {e : Sym2 V} {L : List (Sym2 V)}
    (hhead : tnse_IsNonBridgeEdge (tnse_deleteList A L) e) (htail : tnse_AllNonBridge A L) :
    tnse_AllNonBridge A (e :: L) := ⟨hhead, htail⟩









theorem tnse_connected_deleteList_of_allNonBridge (A : SimpleGraph V) (hA : A.Connected)
    {L : List (Sym2 V)} (hnb : tnse_AllNonBridge A L) :
    (tnse_deleteList A L).Connected := by
  induction L with
  | nil => simpa using hA
  | cons e L ih =>
    obtain ⟨hhead, htail⟩ := hnb
    rw [tnse_deleteList_cons]
    exact tnse_connected_deleteEdge_of_isNonBridge (tnse_deleteList A L) (ih htail) hhead












theorem tnse_reachable_of_detour (A : SimpleGraph V) {a b a' b' : V}
    (h1 : A.Adj a a') (h2 : A.Adj a' b') (h3 : A.Adj b' b)
    (hne1 : s(a, a') ≠ s(a, b)) (hne2 : s(a', b') ≠ s(a, b)) (hne3 : s(b', b) ≠ s(a, b)) :
    (A.deleteEdges {s(a, b)}).Reachable a b := by
  have d1 : (A.deleteEdges {s(a, b)}).Adj a a' :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨h1, by simpa using hne1⟩
  have d2 : (A.deleteEdges {s(a, b)}).Adj a' b' :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨h2, by simpa using hne2⟩
  have d3 : (A.deleteEdges {s(a, b)}).Adj b' b :=
    (SimpleGraph.deleteEdges_adj).mpr ⟨h3, by simpa using hne3⟩
  exact (Walk.cons d1 (Walk.cons d2 (Walk.cons d3 Walk.nil))).reachable






theorem tnse_grid_edge_nonbridge_of_detour (A : SimpleGraph V) {a b a' b' : V}
    (hab : s(a, b) ∈ A.edgeSet)
    (h1 : A.Adj a a') (h2 : A.Adj a' b') (h3 : A.Adj b' b)
    (hne1 : s(a, a') ≠ s(a, b)) (hne2 : s(a', b') ≠ s(a, b)) (hne3 : s(b', b) ≠ s(a, b)) :
    tnse_IsNonBridgeEdge A s(a, b) :=
  ⟨a, b, rfl, hab, tnse_reachable_of_detour A h1 h2 h3 hne1 hne2 hne3⟩









instance tnse_box_finite (R : ℕ) : Finite ↥(box 2 R) := (box_finite 2 R).to_subtype


theorem tnse_site_ne_of_col {x y x' y' : ℤ} (h : x ≠ x') : (![x, y] : Site 2) ≠ ![x', y'] := by
  intro he; exact h (by have := congrFun he 0; simpa using this)


theorem tnse_site_ne_of_row {x y x' y' : ℤ} (h : y ≠ y') : (![x, y] : Site 2) ≠ ![x', y'] := by
  intro he; exact h (by have := congrFun he 1; simpa using this)





theorem tnse_horizEdge_nonbridge {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    tnse_IsNonBridgeEdge (boxInduce R)
      s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
        (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R))) := by
  refine tnse_grid_edge_nonbridge_of_detour (boxInduce R)
    (a' := ⟨![x, y + 1], mem_box2 hx hy1⟩) (b' := ⟨![x + 1, y + 1], mem_box2 hx1 hy1⟩)
    (by rw [SimpleGraph.mem_edgeSet]; exact boxInduce_adj _ _ (hadj_step x y))
    (boxInduce_adj _ _ (vadj_step x y))
    (boxInduce_adj _ _ (hadj_step x (y + 1)))
    (boxInduce_adj _ _ (vadj_step (x + 1) y).symm) ?_ ?_ ?_
  · 
    rw [Ne, Sym2.eq_iff, not_or]
    refine ⟨fun ⟨_, h2⟩ => ?_, fun ⟨h1, _⟩ => ?_⟩
    · exact tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h2)
    · exact tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)
  · 
    rw [Ne, Sym2.eq_iff, not_or]
    refine ⟨fun ⟨h1, _⟩ => ?_, fun ⟨h1, _⟩ => ?_⟩
    · exact tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)
    · exact tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)
  · 
    rw [Ne, Sym2.eq_iff, not_or]
    refine ⟨fun ⟨h1, _⟩ => ?_, fun ⟨_, h2⟩ => ?_⟩
    · exact tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)
    · exact tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h2)

















theorem tnse_deleteList_adj_of_notMem {A : SimpleGraph V} {c d : V} (h : A.Adj c d) :
    ∀ {L : List (Sym2 V)}, s(c, d) ∉ L → (tnse_deleteList A L).Adj c d := by
  intro L
  induction L with
  | nil => intro _; simpa using h
  | cons e L ih =>
    intro hmem
    rw [List.mem_cons, not_or] at hmem
    rw [tnse_deleteList_cons, SimpleGraph.deleteEdges_adj]
    exact ⟨ih hmem.2, by simpa [eq_comm] using hmem.1⟩








theorem tnse_nonbridge_of_detour_notMem {A : SimpleGraph V} {a b a' b' : V} {L : List (Sym2 V)}
    (hab : s(a, b) ∈ (tnse_deleteList A L).edgeSet)
    (h1 : A.Adj a a') (h2 : A.Adj a' b') (h3 : A.Adj b' b)
    (hne1 : s(a, a') ≠ s(a, b)) (hne2 : s(a', b') ≠ s(a, b)) (hne3 : s(b', b) ≠ s(a, b))
    (hL1 : s(a, a') ∉ L) (hL2 : s(a', b') ∉ L) (hL3 : s(b', b) ∉ L) :
    tnse_IsNonBridgeEdge (tnse_deleteList A L) s(a, b) :=
  tnse_grid_edge_nonbridge_of_detour (tnse_deleteList A L) hab
    (tnse_deleteList_adj_of_notMem h1 hL1)
    (tnse_deleteList_adj_of_notMem h2 hL2)
    (tnse_deleteList_adj_of_notMem h3 hL3) hne1 hne2 hne3





def tnse_HasTreeFreeDetour (A : SimpleGraph V) (L : List (Sym2 V)) (e : Sym2 V) : Prop :=
  ∃ a b a' b' : V, e = s(a, b) ∧ s(a, b) ∈ A.edgeSet ∧
    A.Adj a a' ∧ A.Adj a' b' ∧ A.Adj b' b ∧
    s(a, a') ≠ s(a, b) ∧ s(a', b') ≠ s(a, b) ∧ s(b', b) ≠ s(a, b) ∧
    s(a, a') ∉ L ∧ s(a', b') ∉ L ∧ s(b', b) ∉ L












theorem tnse_allNonBridge_of_treeFreeDetour {A : SimpleGraph V} :
    ∀ {L : List (Sym2 V)}, L.Nodup → (∀ e ∈ L, tnse_HasTreeFreeDetour A L e) →
      tnse_AllNonBridge A L := by
  intro L
  induction L with
  | nil => intro _ _; trivial
  | cons e L' ih =>
    intro hnodup hdet
    rw [List.nodup_cons] at hnodup
    obtain ⟨henotin, hnodup'⟩ := hnodup
    refine tnse_allNonBridge_cons ?_ ?_
    · 
      obtain ⟨a, b, a', b', rfl, hab, h1, h2, h3, hne1, hne2, hne3, hL1, hL2, hL3⟩ :=
        hdet e List.mem_cons_self
      
      have hL1' : s(a, a') ∉ L' := fun h => hL1 (List.mem_cons_of_mem _ h)
      have hL2' : s(a', b') ∉ L' := fun h => hL2 (List.mem_cons_of_mem _ h)
      have hL3' : s(b', b) ∉ L' := fun h => hL3 (List.mem_cons_of_mem _ h)
      
      have hadjab : A.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at hab
      have hsurv : s(a, b) ∈ (tnse_deleteList A L').edgeSet := by
        rw [SimpleGraph.mem_edgeSet]
        exact tnse_deleteList_adj_of_notMem hadjab henotin
      exact tnse_nonbridge_of_detour_notMem hsurv h1 h2 h3 hne1 hne2 hne3 hL1' hL2' hL3'
    · 
      refine ih hnodup' (fun f hf => ?_)
      obtain ⟨a, b, a', b', hfe, hab, h1, h2, h3, hne1, hne2, hne3, hL1, hL2, hL3⟩ :=
        hdet f (List.mem_cons_of_mem _ hf)
      exact ⟨a, b, a', b', hfe, hab, h1, h2, h3, hne1, hne2, hne3,
        fun h => hL1 (List.mem_cons_of_mem _ h),
        fun h => hL2 (List.mem_cons_of_mem _ h),
        fun h => hL3 (List.mem_cons_of_mem _ h)⟩







theorem tnse_box_minus_treeFreeDetour_connected {R : ℕ} {L : List (Sym2 ↥(box 2 R))}
    (hnodup : L.Nodup) (hdet : ∀ e ∈ L, tnse_HasTreeFreeDetour (boxInduce R) L e) :
    (tnse_deleteList (boxInduce R) L).Connected :=
  tnse_connected_deleteList_of_allNonBridge (boxInduce R) (boxInduce_connected R)
    (tnse_allNonBridge_of_treeFreeDetour hnodup hdet)








theorem tnse_box_minus_tree_connected {R : ℕ} {L : List (Sym2 ↥(box 2 R))}
    (hnb : tnse_AllNonBridge (boxInduce R) L) :
    (tnse_deleteList (boxInduce R) L).Connected :=
  tnse_connected_deleteList_of_allNonBridge (boxInduce R) (boxInduce_connected R) hnb




theorem tnse_box_minus_nil_connected (R : ℕ) :
    (tnse_deleteList (boxInduce R) []).Connected := by
  simpa using boxInduce_connected R







theorem tnse_box_minus_singleHorizEdge_connected {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    (tnse_deleteList (boxInduce R)
      [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
         (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))]).Connected := by
  apply tnse_box_minus_tree_connected
  refine tnse_allNonBridge_cons ?_ (tnse_allNonBridge_nil _)
  simpa using tnse_horizEdge_nonbridge hx hx1 hy hy1







theorem tnse_singleHorizEdge_treeFreeDetour {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    ∀ e ∈ [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
             (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))],
      tnse_HasTreeFreeDetour (boxInduce R)
        [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
           (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))] e := by
  intro e he
  rw [List.mem_singleton] at he
  subst he
  obtain ⟨a, b, _, hab, hr⟩ := tnse_horizEdge_nonbridge hx hx1 hy hy1
  
  refine ⟨⟨![x, y], mem_box2 hx hy⟩, ⟨![x + 1, y], mem_box2 hx1 hy⟩,
    ⟨![x, y + 1], mem_box2 hx hy1⟩, ⟨![x + 1, y + 1], mem_box2 hx1 hy1⟩, rfl,
    by rw [SimpleGraph.mem_edgeSet]; exact boxInduce_adj _ _ (hadj_step x y),
    boxInduce_adj _ _ (vadj_step x y), boxInduce_adj _ _ (hadj_step x (y + 1)),
    boxInduce_adj _ _ (vadj_step (x + 1) y).symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  
  · rw [Ne, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨_, h2⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h2),
      fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [Ne, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [Ne, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨_, h2⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h2)⟩
  
  · rw [List.mem_singleton, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨_, h2⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h2),
      fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [List.mem_singleton, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨h1, _⟩ => tnse_site_ne_of_row (by omega) (Subtype.ext_iff.mp h1)⟩
  · rw [List.mem_singleton, Sym2.eq_iff, not_or]
    exact ⟨fun ⟨h1, _⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h1),
      fun ⟨_, h2⟩ => tnse_site_ne_of_col (by omega) (Subtype.ext_iff.mp h2)⟩





theorem tnse_box_minus_singleHorizEdge_connected_orderFree {R : ℕ} {x y : ℤ}
    (hx : x.natAbs ≤ R) (hx1 : (x + 1).natAbs ≤ R) (hy : y.natAbs ≤ R) (hy1 : (y + 1).natAbs ≤ R) :
    (tnse_deleteList (boxInduce R)
      [s((⟨![x, y], mem_box2 hx hy⟩ : ↥(box 2 R)),
         (⟨![x + 1, y], mem_box2 hx1 hy⟩ : ↥(box 2 R)))]).Connected :=
  tnse_box_minus_treeFreeDetour_connected (List.nodup_singleton _)
    (tnse_singleHorizEdge_treeFreeDetour hx hx1 hy hy1)





theorem tnse_singleEdge_nonvacuous :
    (tnse_deleteList (boxInduce 2)
      [s((⟨![0, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)),
         (⟨![1, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)))]).Reachable
      (⟨![0, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2))
      (⟨![1, 0], mem_box2 (by decide) (by decide)⟩ : ↥(box 2 2)) :=
  (tnse_box_minus_singleHorizEdge_connected (R := 2) (x := 0) (y := 0)
    (by decide) (by decide) (by decide) (by decide)) _ _















































end Lattice

end StatMech
