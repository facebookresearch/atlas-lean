/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

open Finset List

@[inherit_doc] scoped notation "α(" G ")" => indepNum G

@[simp] lemma indepNum_of_isEmpty [IsEmpty V] : α(G) = 0 := by
  simp [indepNum, isNIndepSet_iff, Subsingleton.elim _ ∅]

@[simp] lemma indepNum_pos [Finite V] [Nonempty V] : 0 < α(G) := by
  cases nonempty_fintype V
  obtain ⟨v⟩ := ‹Nonempty V›
  rw [← Nat.add_one_le_iff]
  exact le_csSup ⟨Nat.card V, by simp [mem_upperBounds, isNIndepSet_iff, Finset.card_le_univ]⟩
    ⟨{v}, by simp [isNIndepSet_iff]⟩

/-- Infinite graphs: definitions for clique number so that the clique number of a graph
with unbounded clique size is `∞` rather than 0.
-/
noncomputable
def ecliqueNum (G : SimpleGraph V) : ℕ∞ := ⨆ (s : Finset V) (_ : G.IsClique s), #s

/-- **Sizes of maximal cliques.** For a simple graph $G$, this is the set of natural numbers $k$
such that some finite clique of $G$ with exactly $k$ vertices is maximal under inclusion among
the finite cliques of $G$, that is, no finite clique of $G$ strictly contains it.

An infinite maximal clique of $G$ contributes no size to this set. -/
def maximalCliqueSizes (G : SimpleGraph V) : Set ℕ :=
  { k | ∃ S : Finset V, Maximal (fun T : Finset V => G.IsClique (T : Set V)) S ∧ S.card = k }

open scoped Classical in
/-- **Triangles containing an edge.** For a simple graph $G$ on a finite vertex set and an edge
$uv$ of $G$, this is the finite set of triangles of $G$ that contain the edge $uv$, where a
triangle is the vertex set of a $3$-clique of $G$; that is, the $3$-cliques of $G$ containing
both $u$ and $v$. -/
noncomputable def trianglesContaining {α : Type*} [Fintype α] (G : SimpleGraph α)
    (uv : G.edgeSet) : Finset (Finset α) :=
  (G.cliqueFinset 3).filter (fun t ↦ uv.1.toFinset ⊆ t)


end SimpleGraph
