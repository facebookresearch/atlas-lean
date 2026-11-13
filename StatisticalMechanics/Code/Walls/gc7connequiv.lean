/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.FluxEdgeCopyBridge
import Code.Walls.gc6_pairingpath

open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FluxEdgeCopy

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]








omit [DecidableEq ι] [Fintype V] [Fintype ι] in


theorem gc7_connK_refl (ends : ι → Sym2 V) (K : Finset ι) (a : V) :
    connK ends K a a :=
  Relation.ReflTransGen.refl

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι] in




theorem gc7_connK_symm (ends : ι → Sym2 V) (K : Finset ι) {a b : V}
    (h : connK ends K a b) : connK ends K b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      rcases hstep with ⟨i, hi, ha, hb, hne⟩
      exact Relation.ReflTransGen.head ⟨i, hi, hb, ha, hne.symm⟩ ih

omit [DecidableEq ι] [Fintype V] [Fintype ι] in


theorem gc7_connK_trans (ends : ι → Sym2 V) (K : Finset ι) {a b c : V}
    (h₁ : connK ends K a b) (h₂ : connK ends K b c) : connK ends K a c :=
  h₁.trans h₂






omit [DecidableEq ι] [Fintype V] [Fintype ι] in



theorem gc7_connK_equivalence (ends : ι → Sym2 V) (K : Finset ι) :
    Equivalence (connK ends K) :=
  ⟨fun a => gc7_connK_refl ends K a,
   fun h => gc7_connK_symm ends K h,
   fun h₁ h₂ => gc7_connK_trans ends K h₁ h₂⟩




def gc7_connSetoid (ends : ι → Sym2 V) (K : Finset ι) : Setoid V :=
  Setoid.mk (connK ends K) (gc7_connK_equivalence ends K)

@[simp] theorem gc7_connSetoid_rel (ends : ι → Sym2 V) (K : Finset ι) {a b : V} :
    (gc7_connSetoid ends K) a b ↔ connK ends K a b := Iff.rfl










theorem gc7_connClasses_isPartition (ends : ι → Sym2 V) (K : Finset ι) :
    Setoid.IsPartition (gc7_connSetoid ends K).classes :=
  (gc7_connSetoid ends K).isPartition_classes








theorem gc7_unique_cluster (ends : ι → Sym2 V) (K : Finset ι) (a : V) :
    ∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ a ∈ C :=
  (gc7_connClasses_isPartition ends K).2 a





theorem gc7_compOf_eq_class (ends : ι → Sym2 V) (K : Finset ι) (u : V) :
    ((compOf ends K u : Finset V) : Set V) = {x | (gc7_connSetoid ends K) x u} := by
  ext x
  simp only [Finset.coe_filter, compOf, Set.mem_setOf_eq, Finset.mem_univ, true_and,
    gc7_connSetoid_rel]
  exact ⟨fun h => gc7_connK_symm ends K h, fun h => gc7_connK_symm ends K h⟩





theorem gc7_compOf_mem_classes (ends : ι → Sym2 V) (K : Finset ι) (u : V) :
    ((compOf ends K u : Finset V) : Set V) ∈ (gc7_connSetoid ends K).classes := by
  rw [gc7_compOf_eq_class]
  exact (gc7_connSetoid ends K).mem_classes u
















theorem gc7_odd_marks_unique_cluster (ends : ι → Sym2 V) (K : Finset ι) (o x y g : V) :
    (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ o ∈ C)
      ∧ (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ x ∈ C)
      ∧ (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ y ∈ C)
      ∧ (∃! C, C ∈ (gc7_connSetoid ends K).classes ∧ g ∈ C) :=
  ⟨gc7_unique_cluster ends K o, gc7_unique_cluster ends K x,
   gc7_unique_cluster ends K y, gc7_unique_cluster ends K g⟩












theorem gc7_pair_in_one_cluster {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (N : Finset (Copy G m)) {i j : V}
    (hbdry : sources (endsM G m) N = {i, j}) (hij : i ≠ j) :
    (gc7_connSetoid (endsM G m) (univ : Finset (Copy G m))) i j := by
  
  exact gc6_pairingPath G m N hbdry hij




theorem gc7_pair_same_class {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ) (N : Finset (Copy G m)) {i j : V}
    (hbdry : sources (endsM G m) N = {i, j}) (hij : i ≠ j) {C : Set V}
    (hC : C ∈ (gc7_connSetoid (endsM G m) (univ : Finset (Copy G m))).classes) :
    i ∈ C ↔ j ∈ C := by
  have hconn : (gc7_connSetoid (endsM G m) (univ : Finset (Copy G m))) i j :=
    gc7_pair_in_one_cluster G m N hbdry hij
  obtain ⟨z, rfl⟩ := hC
  constructor
  · intro hi
    
    exact gc7_connK_trans (endsM G m) univ (gc7_connK_symm (endsM G m) univ hconn) hi
  · intro hj
    exact gc7_connK_trans (endsM G m) univ hconn hj









omit [DecidableEq ι] [Fintype V] [Fintype ι] in






theorem gc7_two_pairs_share_cluster (ends : ι → Sym2 V) (K : Finset ι) {i j k l : V}
    (hij : connK ends K i j) (hkl : connK ends K k l) (hik : connK ends K i k) :
    connK ends K i j ∧ connK ends K i k ∧ connK ends K i l :=
  ⟨hij, hik, gc7_connK_trans ends K hik hkl⟩





theorem gc7_four_marks_one_class (ends : ι → Sym2 V) (K : Finset ι) {i j k l : V}
    (hij : connK ends K i j) (hkl : connK ends K k l) (hik : connK ends K i k) :
    let C := {x : V | (gc7_connSetoid ends K) x i}
    i ∈ C ∧ j ∈ C ∧ k ∈ C ∧ l ∈ C := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact gc7_connK_refl ends K i
  · exact gc7_connK_symm ends K hij
  · exact gc7_connK_symm ends K hik
  · exact gc7_connK_symm ends K (gc7_connK_trans ends K hik hkl)











theorem gc7_nonvacuous :
    Setoid.IsPartition
      (gc7_connSetoid (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2)))
        (univ : Finset (Fin 1))).classes :=
  gc7_connClasses_isPartition _ _




theorem gc7_unique_cluster_nonvacuous (a : Fin 2) :
    ∃! C, C ∈ (gc7_connSetoid (fun _ : Fin 1 => (s(0, 1) : Sym2 (Fin 2)))
        (univ : Finset (Fin 1))).classes ∧ a ∈ C :=
  gc7_unique_cluster _ _ a

end StatMech.Walls
