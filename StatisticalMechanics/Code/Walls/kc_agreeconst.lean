/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































import Mathlib

open scoped BigOperators
open Finset SimpleGraph

namespace StatMech.Walls









section EdgeBoundary

variable {V : Type*} {G : SimpleGraph V} (S : Set V)





def crossesBoundary (e : Sym2 V) : Prop :=
  Sym2.lift ⟨fun u v => (u ∈ S) ≠ (v ∈ S), by
    intro a b; exact propext ⟨fun h => Ne.symm h, fun h => Ne.symm h⟩⟩ e

@[simp] theorem crossesBoundary_mk (u v : V) :
    crossesBoundary S s(u, v) ↔ (u ∈ S) ≠ (v ∈ S) := by
  unfold crossesBoundary; rw [Sym2.lift_mk]

variable (G) in


def edgeBoundary : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet ∧ crossesBoundary S e}



theorem mem_edgeBoundary_iff {u v : V} (h : G.Adj u v) :
    s(u, v) ∈ edgeBoundary G S ↔ (u ∈ S) ≠ (v ∈ S) := by
  unfold edgeBoundary
  rw [Set.mem_setOf_eq, crossesBoundary_mk]
  constructor
  · exact fun h2 => h2.2
  · exact fun h2 => ⟨by rw [SimpleGraph.mem_edgeSet]; exact h, h2⟩

end EdgeBoundary








section LocalStep

variable {V : Type*} {G : SimpleGraph V} {S T : Set V}




theorem agree_bit_adj (hbdy : edgeBoundary G S = edgeBoundary G T)
    {u v : V} (h : G.Adj u v) :
    ((u ∈ S) ↔ (u ∈ T)) ↔ ((v ∈ S) ↔ (v ∈ T)) := by
  
  have hcross : ((u ∈ S) ≠ (v ∈ S)) ↔ ((u ∈ T) ≠ (v ∈ T)) := by
    have hS := mem_edgeBoundary_iff S h
    have hT := mem_edgeBoundary_iff T h
    rw [hbdy] at hS
    exact hS.symm.trans hT
  
  classical
  by_cases huS : u ∈ S <;> by_cases hvS : v ∈ S <;>
    by_cases huT : u ∈ T <;> by_cases hvT : v ∈ T <;>
    simp_all



theorem agree_bit_walk (hbdy : edgeBoundary G S = edgeBoundary G T)
    {x y : V} (w : G.Walk x y) :
    ((x ∈ S) ↔ (x ∈ T)) ↔ ((y ∈ S) ↔ (y ∈ T)) := by
  induction w with
  | nil => rfl
  | cons hadj p ih => exact (agree_bit_adj hbdy hadj).trans ih

end LocalStep






section TheNode

variable {V : Type*} {G : SimpleGraph V} {S T : Set V}















theorem agree_bit_const (hG : G.Preconnected) (hbdy : edgeBoundary G S = edgeBoundary G T)
    (x y : V) :
    ((x ∈ S) ↔ (x ∈ T)) ↔ ((y ∈ S) ↔ (y ∈ T)) :=
  agree_bit_walk hbdy (hG x y).some





theorem agreeBit_const_bool [DecidablePred (· ∈ S)] [DecidablePred (· ∈ T)]
    (hG : G.Preconnected)
    (hbdy : edgeBoundary G S = edgeBoundary G T) (x y : V) :
    (decide (x ∈ S) = decide (x ∈ T)) ↔ (decide (y ∈ S) = decide (y ∈ T)) := by
  have h := agree_bit_const hG hbdy x y
  by_cases hxS : x ∈ S <;> by_cases hxT : x ∈ T <;>
    by_cases hyS : y ∈ S <;> by_cases hyT : y ∈ T <;> simp_all

end TheNode








section Rigidity

variable {V : Type*} {G : SimpleGraph V} {S T : Set V}






theorem eq_or_compl_of_edgeBoundary_eq [Nonempty V] (hG : G.Preconnected)
    (hbdy : edgeBoundary G S = edgeBoundary G T) :
    S = T ∨ (∀ z, z ∈ S ↔ z ∉ T) := by
  classical
  obtain ⟨v₀⟩ := (inferInstance : Nonempty V)
  by_cases h0 : (v₀ ∈ S) ↔ (v₀ ∈ T)
  · 
    left
    apply Set.ext
    intro z
    exact (agree_bit_const hG hbdy v₀ z).mp h0
  · 
    right
    intro z
    have hz : ¬ ((z ∈ S) ↔ (z ∈ T)) := fun hc => h0 ((agree_bit_const hG hbdy v₀ z).mpr hc)
    
    by_cases hzS : z ∈ S <;> by_cases hzT : z ∈ T <;> simp_all

end Rigidity

end StatMech.Walls
