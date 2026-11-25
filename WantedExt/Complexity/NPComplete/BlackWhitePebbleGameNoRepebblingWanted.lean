/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BLACK-WHITE PEBBLE GAME WITHOUT RE-PEBBLING is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4 (1983),
397-411, doi:10.1016/0196-6774(83)90019-6, entry [3] THE PEBBLE GAME and its comment on THE
BLACK-WHITE PEBBLE GAME ("except in the case where re-pebbling is forbidden. Here
NP-completeness reigns"), attributed to Lengauer;
T. Lengauer, "Black-white pebbles and graph separation", Acta Informatica 16 (1981), 465-475,
doi:10.1007/BF00264496 (cited by Johnson as a 1980 manuscript; full text not available here).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BlackWhitePebbleGameNoRepebbling

/-!
# BLACK-WHITE PEBBLE GAME WITHOUT RE-PEBBLING is NP-complete

INSTANCE: an acyclic directed graph `G = (V, A)` with a distinguished vertex `v₀` that is the
only vertex in `V` with out-degree `0` (the root), and a positive integer `k`.
QUESTION: starting with an empty graph, can one pebble the root and then return the graph to an
unpebbled state, with at most `k` pebbles on the graph at any time and no vertex pebbled twice,
obeying the rules of the black-white pebble game (Cook and Sethi)?
- a black pebble can be removed from the graph at any time;
- a black pebble can be placed on a vertex `v` only if all vertices `u` with `(u, v) ∈ A`
  currently contain pebbles;
- a white pebble can be placed on any vertex at any time;
- a white pebble cannot be removed unless all immediate predecessors of its vertex currently
  contain pebbles (the colors of the pebbles on the predecessors do not matter).

Johnson's column states these rules for THE BLACK-WHITE PEBBLE GAME and records that, while the
complexity of the game with re-pebbling is open, the problem is NP-complete when re-pebbling is
forbidden, citing Lengauer. "No vertex pebbled twice" is the one-shot (progressive) restriction:
each vertex receives a pebble, of either color, at most once. A pebbling then has at most
`2|V|` moves, so it is a polynomial certificate.

The vertices are `0, …, n - 1` and the arcs are a list of pairs `(u, v)`, the arc `u → v`, with
no repetitions; `WellFormed` requires acyclicity (no vertex reaches itself by a nonempty
directed path), that `v₀ = r` is a vertex without outgoing arcs while every other vertex has
one, and `0 < k`. A configuration is a pair `(B, W)` of the sets of vertices carrying black and
white pebbles; a pebbling is a sequence of configurations `c 0, …, c T` with `c 0 = c T = (∅, ∅)`
in which each configuration arises from the previous one by one move, every configuration has
at most `k` pebbles, the root carries a pebble in some configuration, and for each vertex there
is at most one step at which it goes from unpebbled to pebbled. A pebble is never placed on a
vertex that already carries one.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n`, the arc list `A` (pairs `(u, v)` for arcs `u → v`), the
root `r`, and the pebble bound `k`. -/
abbrev BlackWhitePebbleGameNoRepebblingInstance := ℕ × List (ℕ × ℕ) × ℕ × ℕ

/-- The digraph of the instance on `Fin n`: `u → v` is an arc iff `(u, v)` is in the arc
list. -/
def Graph (i : BlackWhitePebbleGameNoRepebblingInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- Well-formedness of an instance: the arc list has no repeated arcs and its endpoints are
vertices, the digraph is acyclic, the root `r` is a vertex with no outgoing arc, every other
vertex has an outgoing arc, and `0 < k`. -/
def WellFormed (i : BlackWhitePebbleGameNoRepebblingInstance) : Prop :=
  i.2.1.Nodup ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (Graph i).Adj v v) ∧ i.2.2.1 < i.1 ∧
    (∀ a ∈ i.2.1, a.1 ≠ i.2.2.1) ∧ (∀ v < i.1, v ≠ i.2.2.1 → ∃ a ∈ i.2.1, a.1 = v) ∧
    0 < i.2.2.2

/-- One move of the black-white pebble game from the configuration `c = (B, W)` (black and
white pebbles) to `c'`: place a black pebble on an unpebbled vertex whose predecessors all
carry pebbles, remove a black pebble, place a white pebble on an unpebbled vertex, or remove a
white pebble from a vertex whose predecessors all carry pebbles. -/
def Move (i : BlackWhitePebbleGameNoRepebblingInstance)
    (c c' : Finset (Fin i.1) × Finset (Fin i.1)) : Prop :=
  (∃ v, v ∉ c.1 ∪ c.2 ∧ (∀ u, (Graph i).Adj u v → u ∈ c.1 ∪ c.2) ∧ c' = (insert v c.1, c.2)) ∨
    (∃ v ∈ c.1, c' = (c.1.erase v, c.2)) ∨
    (∃ v, v ∉ c.1 ∪ c.2 ∧ c' = (c.1, insert v c.2)) ∨
    (∃ v ∈ c.2, (∀ u, (Graph i).Adj u v → u ∈ c.1 ∪ c.2) ∧ c' = (c.1, c.2.erase v))

/-- A one-shot black-white pebbling with at most `k` pebbles: configurations `c 0, …, c T`,
empty at both ends, joined by moves, each with at most `k` pebbles, with the root pebbled in
some configuration, and each vertex going from unpebbled to pebbled at most once. -/
def BlackWhitePebbleGameNoRepebblingFeasible (i : BlackWhitePebbleGameNoRepebblingInstance) :
    Prop :=
  ∃ (T : ℕ) (c : ℕ → Finset (Fin i.1) × Finset (Fin i.1)),
    c 0 = (∅, ∅) ∧ c T = (∅, ∅) ∧ (∀ t < T, Move i (c t) (c (t + 1))) ∧
    (∀ t ≤ T, (c t).1.card + (c t).2.card ≤ i.2.2.2) ∧
    (∃ t ≤ T, ∃ v ∈ (c t).1 ∪ (c t).2, (v : ℕ) = i.2.2.1) ∧
    ∀ v, ∀ t < T, ∀ t' < T, v ∉ (c t).1 ∪ (c t).2 → v ∈ (c (t + 1)).1 ∪ (c (t + 1)).2 →
      v ∉ (c t').1 ∪ (c t').2 → v ∈ (c (t' + 1)).1 ∪ (c (t' + 1)).2 → t = t'

open Classical in
/-- BLACK-WHITE PEBBLE GAME WITHOUT RE-PEBBLING as a decision problem over bitstrings. -/
noncomputable def blackWhitePebbleGameNoRepebblingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BlackWhitePebbleGameNoRepebblingInstance) x with
  | some i => decide (WellFormed i ∧ BlackWhitePebbleGameNoRepebblingFeasible i)
  | none => false

/-- **BLACK-WHITE PEBBLE GAME WITHOUT RE-PEBBLING is NP-complete.** Source: Johnson (1983),
NP-completeness column, THE PEBBLE GAME; Lengauer (1981). -/
public theorem_wanted blackWhitePebbleGameNoRepebbling_npComplete :
    blackWhitePebbleGameNoRepebblingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L blackWhitePebbleGameNoRepebblingDec

end MetaMathlibExt.Complexity.NPComplete.BlackWhitePebbleGameNoRepebbling
