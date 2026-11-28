/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ELIMINATION DEGREE SEQUENCE: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT47] ELIMINATION
DEGREE SEQUENCE (attributed there to Garey, Johnson, and Papadimitriou, 1977,
unpublished; transformation from EXACT COVER BY 3-SETS).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EliminationDegreeSequence

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

end MetaMathlibExt.Complexity.NPComplete.EliminationDegreeSequence
