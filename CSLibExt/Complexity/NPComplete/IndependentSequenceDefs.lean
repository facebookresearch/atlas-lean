/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

/-!
# INDEPENDENT SEQUENCE: definitions

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |V|`.
QUESTION: is there an independent sequence for `G` of length at least `K`, i.e., a sequence
`v₁, …, v_m` of independent vertices of `G` with `m ≥ K` such that, for all `i < m`, a vertex
`v̄ᵢ ∈ V` exists which is adjacent to `v_{i+1}` but is not adjacent to any `v_j` for `j ≤ i`?

The sequence is a list `l` (0-indexed, so `v_{i+1}` is `l[i]` and `v₁, …, vᵢ` is `l.take i`)
whose entries form an independent set (Mathlib's `SimpleGraph.IsIndepSet`). The witness
condition forces the entries to be distinct: if `v_{i+1} = v_j` with `j ≤ i`, a vertex adjacent
to `v_{i+1}` is adjacent to `v_j`. The graph is given by a vertex count `n` (vertices `Fin n`)
and a simple edge list. The bound `K ≤ |V|` follows the convention of Garey and Johnson's
[GT20] INDEPENDENT SET.

Halldórsson shows that feasibility of a sequence is checked in polynomial time, so the problem
is in NP, and Proposition 2.3 maps a graph `G` on `v₁, …, vₙ` to the graph `H_G` that adds a
clique `w₁, …, wₙ` with `vᵢ wⱼ` an edge iff `i ≥ j`; `G` has an independent set of size `K`
iff `H_G` has an independent sequence of length `K`, which reduces INDEPENDENT SET to this
problem.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

Source:
M. M. Halldórsson, "Approximations of weighted independent set and hereditary subset
problems", Journal of Graph Algorithms and Applications 4(1) (2000), 1-16,
doi:10.7155/jgaa.00020, Section 2.1, problem Max Independent Sequence (introduced by Blundo)
and Proposition 2.3 (a size-preserving reduction from INDEPENDENT SET);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM INDEPENDENT SEQUENCE.
-/

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
