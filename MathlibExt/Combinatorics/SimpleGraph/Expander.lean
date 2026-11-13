/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Basic.Real.Basic

/-!
# `C`-expanders

Formalizes Definition 1 of Michael Krivelevich, Alan Lew, and Peleg Michaeli,
*Rigidity of expanders and pseudorandom graphs*,
https://arxiv.org/abs/2608.21058v1.

For `C > 0`, an `n`-vertex graph is a `C`-expander when every small vertex set
expands by a factor `C` and any two large disjoint vertex sets have an edge
between them.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- External neighbourhood of `A`: vertices outside `A` adjacent to some vertex of `A`. -/
def externalNeighborSet (A : Set V) : Set V :=
  { v | v ∉ A ∧ ∃ a ∈ A, G.Adj a v }

/-- Membership characterization for the external neighbourhood set. -/
@[simp]
theorem mem_externalNeighborSet (A : Set V) (v : V) :
    v ∈ G.externalNeighborSet A ↔ v ∉ A ∧ ∃ a ∈ A, G.Adj a v :=
  Iff.rfl

/-- The external neighbourhood of `A` is disjoint from `A`. -/
theorem externalNeighborSet_disjoint (A : Set V) :
    Disjoint (G.externalNeighborSet A) A := by
  rw [Set.disjoint_left]
  intro v hv hA
  exact hv.1 hA

/-- An external neighbour comes with an adjacent source vertex in `A`. -/
theorem exists_adj_of_mem_externalNeighborSet {A : Set V} {v : V}
    (h : v ∈ G.externalNeighborSet A) : ∃ a ∈ A, G.Adj a v :=
  h.2

/-- Definition 1 from the source: `C`-expander with a real parameter `C`. -/
@[nolint unusedArguments]
def IsCExpander [Finite V] (C : ℝ) : Prop :=
  0 < C ∧
    (∀ A : Set V, (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C) →
      C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ)) ∧
    ∀ A B : Set V, Disjoint A B →
      (Nat.card V : ℝ) / (2 * C) ≤ (A.ncard : ℝ) →
      (Nat.card V : ℝ) / (2 * C) ≤ (B.ncard : ℝ) →
      ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

/-- A `C`-expander satisfies `0 < C`. -/
theorem IsCExpander.pos [Finite V] {C : ℝ} (h : G.IsCExpander C) : 0 < C :=
  h.1

/-- Small-set expansion clause of a `C`-expander. -/
theorem IsCExpander.small_expansion [Finite V] {C : ℝ} (h : G.IsCExpander C)
    (A : Set V) (hA : (A.ncard : ℝ) < (Nat.card V : ℝ) / (2 * C)) :
    C * (A.ncard : ℝ) ≤ ((G.externalNeighborSet A).ncard : ℝ) :=
  h.2.1 A hA

/-- Large-set edge clause of a `C`-expander. -/
theorem IsCExpander.large_edge [Finite V] {C : ℝ} (h : G.IsCExpander C)
    (A B : Set V) (hdis : Disjoint A B)
    (hA : (Nat.card V : ℝ) / (2 * C) ≤ (A.ncard : ℝ))
    (hB : (Nat.card V : ℝ) / (2 * C) ≤ (B.ncard : ℝ)) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b :=
  h.2.2 A B hdis hA hB

/-- Uniform vertex expansion: every vertex set `S` with `|S| ≤ |V| / 2`
has at least `h * |S|` neighbours outside `S`. -/
@[nolint unusedArguments]
def IsUniformVertexExpander [Finite V] (h : ℝ) : Prop :=
  0 < h ∧
    ∀ S : Set V, (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2 →
      h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ)

/-- A uniform vertex expander satisfies `0 < h`. -/
theorem IsUniformVertexExpander.pos [Finite V] {h : ℝ}
    (hh : G.IsUniformVertexExpander h) : 0 < h :=
  hh.1

/-- Small-set expansion clause of a uniform vertex expander. -/
theorem IsUniformVertexExpander.small_expansion [Finite V] {h : ℝ}
    (hh : G.IsUniformVertexExpander h)
    (S : Set V) (hS : (S.ncard : ℝ) ≤ (Nat.card V : ℝ) / 2) :
    h * (S.ncard : ℝ) ≤ ((G.externalNeighborSet S).ncard : ℝ) :=
  hh.2 S hS

end SimpleGraph
