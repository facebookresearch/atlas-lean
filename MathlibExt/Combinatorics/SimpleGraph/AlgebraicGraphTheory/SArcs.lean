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

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 11, Combinatorics 12, Combinatorics 13, Combinatorics 14

/-!
# SArcs

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 11, Combinatorics 12, Combinatorics 13, Combinatorics 14

## References

* AGT Section 4.1 (for `SimpleGraph.SArc`, `SimpleGraph.IsSArcTransitive`,
  `SimpleGraph.IsSArcRegular`)
* Algebraic Graph Theory, Godsil & Royle (2001), Section 4.2 Arc Graphs, page 61. (for
  `SimpleGraph.arcDigraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 11: $s$-arc

/-- An *s-arc* in a graph is a sequence of vertices (v₀, …, vₛ) such that consecutive vertices are
adjacent and vᵢ₋₁ ≠ vᵢ₊₁ when 0 < i < s.
-/
structure _root_.SimpleGraph.SArc {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) where
  vertices : Fin (s + 1) → V
  adj : ∀ i : Fin s, G.Adj (vertices i.castSucc) (vertices i.succ)
  no_backtrack : ∀ (i : Fin (s + 1)) (h : (i : ℕ) + 2 ≤ s),
    vertices i ≠ vertices ⟨(i : ℕ) + 2, by omega⟩

-- Combinatorics 12: $s$-arc transitive

/-- A graph is *s-arc transitive* if its automorphism group is transitive on s-arcs. -/
def SimpleGraph.IsSArcTransitive {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : Prop :=
  ∀ p q : G.SArc s, ∃ φ : G ≃g G, ∀ i, φ (p.vertices i) = q.vertices i

-- Combinatorics 13: $s$-arc regular

/-- A graph is *s-arc regular* if for any two s-arcs there is a unique aotmorphism mapping the first
to the second.
-/
def SimpleGraph.IsSArcRegular {V : Type*} [Fintype V] (G : SimpleGraph V) (s : ℕ) : Prop :=
  Nonempty (G.SArc s) ∧
  ∀ p q : G.SArc s, ∃! φ : G ≃g G, ∀ i : Fin (s + 1), φ (p.vertices i) = q.vertices i

-- Combinatorics 14: $X^{(s)}$

def _root_.SimpleGraph.SArc.tail {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a : G.SArc (s + 1)) : G.SArc s where
  vertices i := a.vertices ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
  adj i := a.adj ⟨i.val, by omega⟩
  no_backtrack i hi := a.no_backtrack ⟨i.val, Nat.lt_of_lt_of_le i.is_lt (Nat.le_succ _)⟩
    (Nat.le_succ_of_le hi)

def _root_.SimpleGraph.SArc.head {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a : G.SArc (s + 1)) : G.SArc s where
  vertices i := a.vertices ⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩
  adj i := a.adj ⟨i.val + 1, by omega⟩
  no_backtrack i hi := a.no_backtrack ⟨i.val + 1, Nat.succ_lt_succ i.is_lt⟩
    (Nat.succ_le_succ hi)

def _root_.SimpleGraph.SArc.follows {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ} (a b : G.SArc s) : Prop :=
  ∃ c : G.SArc (s + 1), c.head = a ∧ c.tail = b

/-- If s ≥ 1 and α = (x₀, …, xₛ), we define its *head* to be the (s-1)-arc (x₁, …, xₛ) and its
*tail* to be the (s-1)-arc (x₀, …, xₛ₋₁). If α and β are s-arcs we say that β *follows* α if there
is an (s+1)-arc whose tail is α and whose head is β. We use X⁽ˢ⁾ to denote the directed graph with
the s-arcs of X as its vertices, such that (α, β) is an arc if and only if β follows α.
-/
def _root_.SimpleGraph.arcDigraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : ℕ) : Digraph (G.SArc s) where
  Adj a b := b.follows a

end MetaMathlibExt

end
