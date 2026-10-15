/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fin.VecNotation
/-!
# SArcs

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 11, Combinatorics 12, Combinatorics 13, Combinatorics 14
-/

@[expose] public section

-- Combinatorics 11: $s$-arc
structure SimpleGraph.SArc {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) where
  vertices : Fin (s + 1) → V
  adj : ∀ i : Fin s, G.Adj (vertices i.castSucc) (vertices i.succ)
  no_backtrack : ∀ (i : Fin (s + 1)) (h : (i : ℕ) + 2 ≤ s),
    vertices i ≠ vertices ⟨(i : ℕ) + 2, by omega⟩

-- Combinatorics 12: $s$-arc transitive
def SimpleGraph.IsSArcTransitive {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ p q : G.SArc s, ∃ φ : G ≃g G, ∀ i, φ (p.vertices i) = q.vertices i

-- Combinatorics 13: $s$-arc regular
def SimpleGraph.IsSArcRegular {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : Prop :=
  Nonempty (G.SArc s) ∧
  ∀ p q : G.SArc s, ∃! φ : G ≃g G, ∀ i : Fin (s + 1), φ (p.vertices i) = q.vertices i

-- Combinatorics 14: $X^{(s)}$
def SimpleGraph.SArc.tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a : G.SArc (s + 1)) : G.SArc s where
  vertices i := a.vertices ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
  adj i := a.adj ⟨i.val, by omega⟩
  no_backtrack i hi := a.no_backtrack ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
    (Nat.le_succ_of_le hi)


def SimpleGraph.SArc.head {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a : G.SArc (s + 1)) : G.SArc s where
  vertices i := a.vertices ⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩
  adj i := a.adj ⟨i.val + 1, by omega⟩
  no_backtrack i hi := a.no_backtrack ⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩
    (Nat.succ_le_succ hi)


def SimpleGraph.SArc.follows {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a b : G.SArc s) : Prop :=
  ∃ c : G.SArc (s + 1), c.head = a ∧ c.tail = b


def SimpleGraph.arcDigraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) : Digraph (G.SArc s) where
  Adj a b := b.follows a


abbrev K₃ : SimpleGraph (Fin 3) := SimpleGraph.completeGraph (Fin 3)


abbrev a012 : K₃.SArc 2 := ⟨![0, 1, 2], by decide, by decide⟩

abbrev a01 : K₃.SArc 1 := ⟨![0, 1], by decide, by decide⟩

abbrev a12 : K₃.SArc 1 := ⟨![1, 2], by decide, by decide⟩


@[ext] theorem SimpleGraph.SArc.ext {V : Type*} [Fintype V] {G : SimpleGraph V} {s : ℕ}
    {a b : G.SArc s} (h : a.vertices = b.vertices) : a = b := by
  cases a; cases b; simp_all

example : (K₃.arcDigraph 1).Adj a01 a12 :=
  ⟨a012, by apply SimpleGraph.SArc.ext; decide,
          by apply SimpleGraph.SArc.ext; decide⟩

end
