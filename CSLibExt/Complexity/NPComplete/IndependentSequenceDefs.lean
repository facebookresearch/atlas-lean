/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SEQUENCE: definitions

Source:
M. M. Halldórsson, "Approximations of weighted independent set and hereditary subset
problems", Journal of Graph Algorithms and Applications 4(1) (2000), 1-16,
doi:10.7155/jgaa.00020, Section 2.1, problem Max Independent Sequence (introduced by Blundo)
and Proposition 2.3 (a size-preserving reduction from INDEPENDENT SET);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM INDEPENDENT SEQUENCE.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSequence

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev IndependentSequenceInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : IndependentSequenceInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`, and
`0 < K ≤ |V|`. -/
def WellFormed (i : IndependentSequenceInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- `l` is an independent sequence of `G`: its entries are independent, and for every `i` with
`i + 1 < |l|` some vertex is adjacent to `l[i + 1]` but to none of `l[0], …, l[i]`. -/
def IsIndependentSequence {n : ℕ} (G : SimpleGraph (Fin n)) (l : List (Fin n)) : Prop :=
  G.IsIndepSet {v | v ∈ l} ∧
    ∀ (i : ℕ) (hi : i + 1 < l.length), ∃ w : Fin n, G.Adj w l[i + 1] ∧
      ∀ u ∈ l.take (i + 1), ¬ G.Adj w u

/-- Some independent sequence of `G` has length at least `K`. -/
def IndependentSequenceFeasible (i : IndependentSequenceInstance) : Prop :=
  ∃ l : List (Fin i.1), i.2.2 ≤ l.length ∧ IsIndependentSequence (Graph i) l

open Classical in
/-- INDEPENDENT SEQUENCE as a decision problem over bitstrings. -/
noncomputable def independentSequenceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IndependentSequenceInstance) x with
  | some i => decide (WellFormed i ∧ IndependentSequenceFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSequence
