/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







import Mathlib
import Code.Walls.bkfforest

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}










theorem bkt_bot_reachable_iff {V : Type*} (t t' : V) :
    (⊥ : SimpleGraph V).Reachable t t' ↔ t = t' := by
  constructor
  · intro h
    obtain ⟨p⟩ := h
    cases p with
    | nil => rfl
    | cons hadj _ => exact absurd hadj (by simp)
  · rintro rfl; exact Reachable.refl _























noncomputable def bkt_ctrMap (L : ℕ) (y : Site d) : Site d → Option (Site d) := by
  classical
  exact fun x => if x ∈ bc61_boxAround d L y then none else some x






noncomputable def bkt_ctrGraph (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    SimpleGraph (Option (Site d)) where
  Adj u v :=
    match u, v with
    | some a, some b =>
        a ∉ bc61_boxAround d L y ∧ b ∉ bc61_boxAround d L y ∧ (openSubgraph d ω).Adj a b
    | none, some a => a ∉ bc61_boxAround d L y ∧ bc67_GnIncident ω L y a
    | some a, none => a ∉ bc61_boxAround d L y ∧ bc67_GnIncident ω L y a
    | none, none => False
  symm := by
    rintro u v h
    cases u <;> cases v <;> simp_all [SimpleGraph.adj_comm]
  loopless := by
    refine ⟨fun u h => ?_⟩
    cases u with
    | none => exact h
    | some a => exact (openSubgraph d ω).loopless.irrefl a h.2.2

@[simp] theorem bkt_ctrGraph_some_some (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bkt_ctrGraph ω L y).Adj (some a) (some b) ↔
      a ∉ bc61_boxAround d L y ∧ b ∉ bc61_boxAround d L y ∧ (openSubgraph d ω).Adj a b :=
  Iff.rfl

@[simp] theorem bkt_ctrGraph_none_some (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d) :
    (bkt_ctrGraph ω L y).Adj none (some a) ↔
      a ∉ bc61_boxAround d L y ∧ bc67_GnIncident ω L y a :=
  Iff.rfl

@[simp] theorem bkt_ctrGraph_none_none (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    ¬ (bkt_ctrGraph ω L y).Adj none none :=
  id









theorem bkt_deleteSuper_adj_iff (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Adj (some a) (some b) ↔
      (bc67_contractedLattice ω L y).Adj a b := by
  rw [SimpleGraph.deleteIncidenceSet_adj]
  simp only [bkt_ctrGraph_some_some, ne_eq, reduceCtorEq, not_false_eq_true, and_true]
  rw [bc67_contractedLattice_adj]
  constructor
  · rintro ⟨ha, hb, hlat, hopen⟩
    refine ⟨hlat, ?_⟩
    rw [bc61_removeBox_apply_of_notMem ha hb ω]; exact hopen
  · rintro ⟨hlat, hcut⟩
    
    have hane : a ∉ bc61_boxAround d L y := by
      intro hmem
      have : removeSites (bc61_boxAround d L y) ω s(a, b) = false := by
        unfold removeSites; rw [if_pos ⟨a, hmem, by simp⟩]
      rw [this] at hcut; exact absurd hcut (by simp)
    have hbne : b ∉ bc61_boxAround d L y := by
      intro hmem
      have : removeSites (bc61_boxAround d L y) ω s(a, b) = false := by
        unfold removeSites; rw [if_pos ⟨b, hmem, by simp⟩]
      rw [this] at hcut; exact absurd hcut (by simp)
    refine ⟨hane, hbne, hlat, ?_⟩
    rw [← bc61_removeBox_apply_of_notMem hane hbne ω]; exact hcut









theorem bkt_deleteSuper_none_isolated (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (v : Option (Site d)) : ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Adj none v := by
  rw [SimpleGraph.deleteIncidenceSet_adj]; rintro ⟨_, h, _⟩; exact h rfl




theorem bkt_deleteSuper_reachable_of_boxCut (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d)
    (h : (bc67_contractedLattice ω L y).Reachable a b) :
    ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons a c b hadj q ih =>
    exact (Adj.reachable ((bkt_deleteSuper_adj_iff ω L y a c).mpr hadj)).trans ih




theorem bkt_boxCut_reachable_of_deleteSuper (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {u v : Option (Site d)} (h : ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable u v) :
    ∀ a b : Site d, u = some a → v = some b → (bc67_contractedLattice ω L y).Reachable a b := by
  obtain ⟨p⟩ := h
  induction p with
  | nil =>
    rintro a b rfl hb; rw [Option.some_inj.mp hb.symm]
  | @cons u c v hadj q ih =>
    rintro a b rfl hb
    
    cases c with
    | none => exact absurd hadj (by
        have := (SimpleGraph.deleteIncidenceSet_adj).mp hadj
        exact fun _ => this.2.2 rfl)
    | some c' =>
      have hstep : (bc67_contractedLattice ω L y).Adj a c' :=
        (bkt_deleteSuper_adj_iff ω L y a c').mp hadj
      exact (Adj.reachable hstep).trans (ih c' b rfl hb)





theorem bkt_ctr_deleteSuper_eq_boxCut (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) ↔
      (bc67_contractedLattice ω L y).Reachable a b :=
  ⟨fun h => bkt_boxCut_reachable_of_deleteSuper ω L y h a b rfl rfl,
   bkt_deleteSuper_reachable_of_boxCut ω L y a b⟩














theorem bkt_perHub_cutTransfer (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d)
    (hcut : ¬ (bc67_contractedLattice ω L y).Reachable a b) :
    ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) := by
  rw [bkt_ctr_deleteSuper_eq_boxCut]; exact hcut



























theorem bkt_secondBox_not_contracted (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d)
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y)
    (hopen : (openSubgraph d ω).Adj a b) :
    (bkt_ctrGraph ω L y).Adj (some a) (some b) :=
  ⟨ha, hb, hopen⟩


































theorem bkt_box_overconnects (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d)
    (ha : a ∉ bc61_boxAround d L y) (hb : b ∉ bc61_boxAround d L y)
    (hia : bc67_GnIncident ω L y a) (hib : bc67_GnIncident ω L y b) :
    (bkt_ctrGraph ω L y).Reachable (some a) (some b) :=
  (Adj.reachable (G := bkt_ctrGraph ω L y) (by exact ⟨ha, hia⟩ : (bkt_ctrGraph ω L y).Adj (some a) none)).trans
    (Adj.reachable (by exact ⟨hb, hib⟩ : (bkt_ctrGraph ω L y).Adj none (some b)))











theorem bkt_nonvacuous (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    Nonempty (Option (Site d)) ∧
    ∀ a b : Site d,
      (((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) ↔
        (bc67_contractedLattice ω L y).Reachable a b) :=
  ⟨⟨none⟩, fun a b => bkt_ctr_deleteSuper_eq_boxCut ω L y a b⟩











































theorem bkt_status (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) :
    
    (∀ (y a b : Site d),
      ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b) ↔
        (bc67_contractedLattice ω L y).Reachable a b) ∧
    
    (∀ (y a b : Site d), ¬ (bc67_contractedLattice ω L y).Reachable a b →
      ¬ ((bkt_ctrGraph ω L y).deleteIncidenceSet none).Reachable (some a) (some b)) ∧
    
    (∀ (y a b : Site d), a ∉ bc61_boxAround d L y → b ∉ bc61_boxAround d L y →
      bc67_GnIncident ω L y a → bc67_GnIncident ω L y b →
      (bkt_ctrGraph ω L y).Reachable (some a) (some b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y a b; exact bkt_ctr_deleteSuper_eq_boxCut ω L y a b
  · intro y a b hcut; exact bkt_perHub_cutTransfer ω L y a b hcut
  · intro y a b ha hb hia hib; exact bkt_box_overconnects ω L y a b ha hb hia hib

end StatMech.Walls
