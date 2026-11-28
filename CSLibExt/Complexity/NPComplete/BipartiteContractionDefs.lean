/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE CONTRACTION: definitions

Source:
P. Heggernes, P. van 't Hof, D. Lokshtanov and C. Paul, "Obtaining a bipartite graph by
contracting few edges", SIAM Journal on Discrete Mathematics 27(4) (2013), 2143-2156,
doi:10.1137/130907392 (arXiv:1102.5441), Sections 1, 2 and 5.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteContraction

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K` on the number of
contractions. -/
abbrev BipartiteContractionInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BipartiteContractionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BipartiteContractionInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- At most `K` edge contractions turn the graph into a bipartite graph: some map
`f : Fin n → Fin m` has fibers inducing connected subgraphs, `n ≤ m + K` (the contractions
number `n - m`), and the quotient graph is bipartite. -/
def BipartiteContractionFeasible (i : BipartiteContractionInstance) : Prop :=
  ∃ (m : ℕ) (f : Fin i.1 → Fin m), (∀ x, ((Graph i).induce {v | f v = x}).Connected) ∧
    i.1 ≤ m + i.2.2 ∧ ((Graph i).map f).IsBipartite

open Classical in
/-- BIPARTITE CONTRACTION as a decision problem over bitstrings. -/
noncomputable def bipartiteContractionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BipartiteContractionInstance) x with
  | some i => decide (WellFormed i ∧ BipartiteContractionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BipartiteContraction
