/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BLACK-WHITE PEBBLE GAME WITHOUT RE-PEBBLING: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4 (1983),
397-411, doi:10.1016/0196-6774(83)90019-6, entry [3] THE PEBBLE GAME and its comment on THE
BLACK-WHITE PEBBLE GAME ("except in the case where re-pebbling is forbidden. Here
NP-completeness reigns"), attributed to Lengauer;
T. Lengauer, "Black-white pebbles and graph separation", Acta Informatica 16 (1981), 465-475,
doi:10.1007/BF00264496 (cited by Johnson as a 1980 manuscript; full text not available here).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BlackWhitePebbleGameNoRepebbling

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

end MetaMathlibExt.Complexity.NPComplete.BlackWhitePebbleGameNoRepebbling
