/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TOPOLOGICAL MINOR TESTING: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN2] SUBGRAPH HOMEOMORPHISM
(FOR A FIXED GRAPH H), p. 285, comment: "If H is allowed to vary as part of the instance, the
problem is NP-complete, since it contains HAMILTONIAN CIRCUIT as a special case";
R. M. Karp, "Reducibility among combinatorial problems", in *Complexity of Computer
Computations*, Plenum Press (1972), 85-103, doi:10.1007/978-1-4684-2001-2_9
(HAMILTONIAN CIRCUIT, Garey and Johnson's [GT37]).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting

/-- An instance: the vertex count `n` and edge list of `G`, and the vertex count `m` and edge
list of `H`. -/
abbrev TopologicalMinorTestingInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The host graph `G` of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : TopologicalMinorTestingInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: both edge lists are simple (endpoints in range, no
self-loops, no repeated or reversed edges). -/
def WellFormed (i : TopologicalMinorTestingInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.2.Nodup ∧
      ∀ e ∈ i.2.2.2, e.1 < i.2.2.1 ∧ e.2 < i.2.2.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2.2)

/-- `G` contains a subdivision of `H`: a one-to-one map `φ` from the vertices of `H` to those of
`G`, and for each edge `(a, b)` of `H` (the `j`-th list entry) a path in `G` from `φ a` to
`φ b`, such that every branch vertex `φ c` on path `j` is one of its two ends, and every vertex
common to two different paths is a branch vertex. -/
def TopologicalMinorTestingFeasible (i : TopologicalMinorTestingInstance) : Prop :=
  ∃ (φ : Fin i.2.2.1 → Fin i.1)
    (paths : Fin i.2.2.2.length → (u : Fin i.1) × (v : Fin i.1) × (Graph i).Walk u v),
    Function.Injective φ ∧
    (∀ j, ∃ a b : Fin i.2.2.1, (a : ℕ) = (i.2.2.2.get j).1 ∧ (b : ℕ) = (i.2.2.2.get j).2 ∧
      (paths j).1 = φ a ∧ (paths j).2.1 = φ b ∧ (paths j).2.2.IsPath) ∧
    (∀ j, ∀ w ∈ (paths j).2.2.support, ∀ c, φ c = w → w = (paths j).1 ∨ w = (paths j).2.1) ∧
    ∀ j l, j ≠ l → ∀ w ∈ (paths j).2.2.support, w ∈ (paths l).2.2.support → ∃ c, φ c = w

open Classical in
/-- TOPOLOGICAL MINOR TESTING as a decision problem over bitstrings. -/
noncomputable def topologicalMinorTestingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TopologicalMinorTestingInstance) x with
  | some i => decide (WellFormed i ∧ TopologicalMinorTestingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.TopologicalMinorTesting
