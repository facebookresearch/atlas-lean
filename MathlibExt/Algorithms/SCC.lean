/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Relation

variable {V : Type*}

@[expose] public section

/-- Reachability in a directed graph given by its edge
relation: the reflexive-transitive closure. -/
def Reach (E : V → V → Prop) (x y : V) : Prop :=
  Relation.ReflTransGen E x y

/-- The reversed graph's edge relation. -/
def RevE (E : V → V → Prop) (x y : V) : Prop := E y x

/-- Strong connectedness is unchanged by reversing all edges
(the fact Kosaraju's algorithm rests on): reachability in the
reversed graph is reversed reachability, so the strongly
connected components of a graph and its reversal coincide. -/
theorem reach_rev {E : V → V → Prop} (x y : V) :
    Reach (RevE E) x y ↔ Reach E y x := by
  exact Relation.reflTransGen_swap

/-- The strongly connected components (mutual-reachability
classes) of a graph and its reversal are the same. -/
theorem scc_eq_scc_rev {E : V → V → Prop} (x y : V) :
    (Reach (RevE E) x y ∧ Reach (RevE E) y x) ↔
      (Reach E x y ∧ Reach E y x) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(reach_rev y x).mp h2, (reach_rev x y).mp h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(reach_rev x y).mpr h2, (reach_rev y x).mpr h1⟩

/-- Reachability is reflexive and transitive (it is a preorder,
hence descends to a partial order on components). -/
theorem reach_refl {E : V → V → Prop} (x : V) : Reach E x x := by
  exact Relation.ReflTransGen.refl

theorem reach_trans {E : V → V → Prop} {x y z : V}
    (h₁ : Reach E x y) (h₂ : Reach E y z) : Reach E x z := by
  exact Relation.ReflTransGen.trans h₁ h₂
