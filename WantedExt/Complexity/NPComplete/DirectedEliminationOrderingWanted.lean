/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED ELIMINATION ORDERING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT46] DIRECTED
ELIMINATION ORDERING;
D. J. Rose and R. E. Tarjan, "Algorithmic aspects of vertex elimination on
directed graphs", SIAM Journal on Applied Mathematics 34 (1978), 176-197,
doi:10.1137/0134014.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Batteries.Data.List.Basic
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedEliminationOrdering

/-!
# DIRECTED ELIMINATION ORDERING is NP-complete

INSTANCE: a directed graph `G = (V, A)` and a non-negative integer `K`.
QUESTION: is there an elimination ordering for `G` with fill-in `K` or less, i.e., a one-to-one
function `f : V → {1, 2, ..., |V|}` such that there are at most `K` pairs of vertices
`(u, v) ∈ (V × V) - A` with the property that `G` contains a directed path from `u` to `v` that
only passes through vertices `w` satisfying `f(w) < min {f(u), f(v)}`?

A directed path is a list of distinct vertices `u = x₀, x₁, ..., xₖ = v` with `(xⱼ, xⱼ₊₁) ∈ A`;
it "passes through" its interior vertices `x₁, ..., xₖ₋₁`. Since the vertices of a path are
distinct, the pairs counted have `u ≠ v`. Rose and Tarjan (1978, Lemma 1) show that these pairs
are exactly the arcs added by eliminating the vertices in the order `f`, where eliminating `w`
adds an arc `(x, y)` for every remaining `x ≠ y` with `(x, w)` and `(w, y)` present.

Directed graphs are given by arc lists without loops or repeated arcs (Rose and Tarjan:
`E ⊆ {(v, w) | v ≠ w}`), read as Mathlib `Digraph`s. Positions are 0-based:
`f : Fin |V| → Fin |V|`; only comparisons of positions matter.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), arc list, and the bound `K`. -/
abbrev DirectedEliminationOrderingInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The directed graph on `Fin n` whose arcs are the pairs listed in `as`. -/
def digraphOfArcs (n : ℕ) (as : List (ℕ × ℕ)) : Digraph (Fin n) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ as

/-- The directed graph `G = (V, A)` of the instance. -/
def Graph (i : DirectedEliminationOrderingInstance) : Digraph (Fin i.1) :=
  digraphOfArcs i.1 i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs, no loops, and endpoints
in range. -/
def WellFormed (i : DirectedEliminationOrderingInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- `G` contains a directed path `u = x₀, x₁, ..., xₖ = v` (distinct vertices, consecutive
vertices joined by arcs) whose interior vertices `w` all satisfy `f w < min (f u) (f v)`. -/
def FillPath {n : ℕ} (G : Digraph (Fin n)) (f : Fin n → Fin n) (u v : Fin n) : Prop :=
  ∃ ws : List (Fin n), (∀ w ∈ ws, f w < min (f u) (f v)) ∧
    (u :: (ws ++ [v])).IsChain G.Adj ∧ (u :: (ws ++ [v])).Nodup

/-- An elimination ordering with fill-in at most `K`: a one-to-one `f` such that at most `K`
pairs `(u, v)` that are not arcs are joined by a `FillPath`. -/
def DirectedEliminationOrderingFeasible (i : DirectedEliminationOrderingInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.1, Function.Injective f ∧
    {p : Fin i.1 × Fin i.1 | ¬ (Graph i).Adj p.1 p.2 ∧ FillPath (Graph i) f p.1 p.2}.ncard ≤ i.2.2

open Classical in
/-- DIRECTED ELIMINATION ORDERING as a decision problem over bitstrings. -/
noncomputable def directedEliminationOrderingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedEliminationOrderingInstance) x with
  | some i => decide (WellFormed i ∧ DirectedEliminationOrderingFeasible i)
  | none => false

/-- **DIRECTED ELIMINATION ORDERING is NP-complete.** Source: Garey and Johnson (1979),
[GT46]; Rose and Tarjan (1978). -/
public theorem_wanted directedEliminationOrdering_npComplete :
    directedEliminationOrderingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedEliminationOrderingDec

end MetaMathlibExt.Complexity.NPComplete.DirectedEliminationOrdering
