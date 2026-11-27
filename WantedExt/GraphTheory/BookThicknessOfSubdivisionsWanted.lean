/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Book Thickness of Subdivisions
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted

/-! Source record `OPG-34908`. Book thickness of a graph versus its once-subdivided graph:
whether `bt(G)` is bounded by a function of `bt(G')`. -/

/-- Two unordered pairs `e₁ e₂` cross with respect to the spine relation `r`:
    some two distinct endpoints `v ≺ x ≺ w ≺ y` interleave, i.e. `e₁ = {v, w}`
    and `e₂ = {x, y}` with `r v x ∧ r x w ∧ r w y` (or the symmetric pattern
    with the roles of the edges exchanged). -/
def IsCrossing {V : Type} (r : V → V → Prop) (e₁ e₂ : Sym2 V) : Prop :=
  ∃ v w x y : V, v ∈ e₁ ∧ w ∈ e₁ ∧ v ≠ w ∧ x ∈ e₂ ∧ y ∈ e₂ ∧ x ≠ y ∧
    ((r v x ∧ r x w ∧ r w y) ∨ (r x v ∧ r v y ∧ r y w))

/-- A `k`-page book embedding of `G`: a spine embedding plus a (non-proper)
    `k`-colouring of the edges such that same-colour edges never cross. -/
def HasBookEmbedding {V : Type} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (pos : V → ℕ) (_ : Function.Injective pos) (color : ↥G.edgeSet → Fin k),
    ∀ e₁ e₂ : ↥G.edgeSet,
      IsCrossing (fun a b => pos a < pos b) (↑e₁ : Sym2 V) (↑e₂ : Sym2 V) →
        color e₁ ≠ color e₂

/-- `G'` is the graph obtained by subdividing each edge of `G` exactly once:
    every vertex of `G'` is either an old vertex (`old a`) or a new midpoint
    vertex (`mid e`), and each midpoint `mid e` is adjacent exactly to the old
    endpoints of `e` (hence old vertices are never adjacent to each other). -/
def IsEdgeSubdivision {V V' : Type} (G : SimpleGraph V) (G' : SimpleGraph V')
    (old : V → V') (mid : ↥G.edgeSet → V') : Prop :=
  Function.Injective old ∧
  Function.Injective mid ∧
  (∀ (a : V) (e : ↥G.edgeSet), old a ≠ mid e) ∧
  (∀ w' : V', (∃ a : V, old a = w') ∨ ∃ e : ↥G.edgeSet, mid e = w') ∧
  (∀ (e : ↥G.edgeSet) (a : V), a ∈ (↑e : Sym2 V) → G'.Adj (old a) (mid e)) ∧
  (∀ (e : ↥G.edgeSet) (w' : V'), G'.Adj (mid e) w' →
    ∃ a : V, a ∈ (↑e : Sym2 V) ∧ w' = old a) ∧
  (∀ (a : V) (w' : V'), G'.Adj (old a) w' →
    ∃ e : ↥G.edgeSet, a ∈ (↑e : Sym2 V) ∧ w' = mid e)

/-- Exact-once specialization of the Blankenship–Oporowski conjecture (OPG-34908):
    book thickness of any finite graph is bounded by a function of the book
    thickness of its once-subdivided graph. -/
def conjecture : Prop :=
  ∃ f : ℕ → ℕ,
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V)
      (V' : Type) [Fintype V'] (G' : SimpleGraph V')
      (old : V → V') (mid : ↥G.edgeSet → V') (k : ℕ),
      IsEdgeSubdivision G G' old mid →
        HasBookEmbedding G' k → HasBookEmbedding G (f k)

/--
Not settled by the cited source: arXiv:2011.04195 refutes the bounded-subdivisions conjecture of
Blankenship and Oporowski, not this exact-once specialization. That conjecture (Conjecture 1
there) asks for `f` with `sn(G) ≤ f(sn(G'), k)` for every subdivision `G'` of `G` with at most `k`
division vertices per edge, where the stack-number `sn` is the book thickness. By Dujmović and
Wood's lemma every graph `G` has a 3-stack subdivision with `1 + 2⌈log₂ qn(G)⌉` division vertices
per edge, so the 5-subdivision of each graph `S_b □ H_n` of Theorem 1 (queue-number at most 4,
stack-number unbounded) has a 3-stack layout. That argument uses five division vertices per edge
and gives no bound on the book thickness of once-subdivided graphs, so it does not decide
`conjecture`: this statement records a wanted answer, not a known one. Source: V. Dujmović,
D. Eppstein, R. Hickingbotham, P. Morin and D. R. Wood, Stack-number is not bounded by
queue-number, Combinatorica 42 (2022), 151-164, https://doi.org/10.1007/s00493-021-4585-7,
arXiv:2011.04195, https://arxiv.org/abs/2011.04195 (Theorem 1 and the paragraph 'Subdivisions'
of the introduction). Moved from `OpenConjectures/GraphTheory/BookThicknessOfSubdivisions`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.BookThicknessOfSubdivisionsWanted
