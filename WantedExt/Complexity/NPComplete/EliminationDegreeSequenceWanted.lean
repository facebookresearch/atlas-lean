/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ELIMINATION DEGREE SEQUENCE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT47] ELIMINATION
DEGREE SEQUENCE (attributed there to Garey, Johnson, and Papadimitriou, 1977,
unpublished; transformation from EXACT COVER BY 3-SETS).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EliminationDegreeSequence

/-!
# ELIMINATION DEGREE SEQUENCE is NP-complete

INSTANCE: a graph `G = (V, E)` and a sequence `⟨d₁, d₂, ..., d_|V|⟩` of non-negative integers
not exceeding `|V| - 1`. QUESTION: is there a one-to-one function `f : V → {1, 2, ..., |V|}`
such that, for `1 ≤ i ≤ |V|`, if `f(v) = i` then there are exactly `dᵢ` vertices `u` such that
`f(u) > i` and `{u, v} ∈ E`?

That is, when the vertices are removed in the order given by `f`, each vertex has exactly the
prescribed number of neighbours among the vertices not yet removed. (Garey and Johnson note that
the variant counting all neighbours of `v` is trivially solvable in polynomial time.)

Positions are 0-based here: `f : Fin |V| → Fin |V|` and position `i` reads `dᵢ₊₁`, the entry
of the list at index `i`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the sequence
`⟨d₁, ..., dₙ⟩` as a list. -/
abbrev EliminationDegreeSequenceInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : EliminationDegreeSequenceInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the sequence has
exactly `n` entries, and every entry is at most `n - 1`. -/
def WellFormed (i : EliminationDegreeSequenceInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1 ∧ ∀ d ∈ i.2.2, d ≤ i.1 - 1

/-- A one-to-one `f : V → {0, ..., n - 1}` such that every vertex `v` has exactly `d_{f v}`
neighbours `u` with `f v < f u`. -/
def EliminationDegreeSequenceFeasible (i : EliminationDegreeSequenceInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.1, Function.Injective f ∧
    ∀ v : Fin i.1, {u : Fin i.1 | f v < f u ∧ (Graph i).Adj u v}.ncard = i.2.2.getD (f v) 0

open Classical in
/-- ELIMINATION DEGREE SEQUENCE as a decision problem over bitstrings. -/
noncomputable def eliminationDegreeSequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EliminationDegreeSequenceInstance) x with
  | some i => decide (WellFormed i ∧ EliminationDegreeSequenceFeasible i)
  | none => false

/-- **ELIMINATION DEGREE SEQUENCE is NP-complete.** Source: Garey and Johnson (1979), [GT47]
(Garey, Johnson, and Papadimitriou, 1977, unpublished). -/
public theorem_wanted eliminationDegreeSequence_npComplete :
    eliminationDegreeSequenceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eliminationDegreeSequenceDec

end MetaMathlibExt.Complexity.NPComplete.EliminationDegreeSequence
