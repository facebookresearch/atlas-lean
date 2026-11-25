/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DEGREE CONSTRAINED SPANNING TREE for fixed K ≥ 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND1] DEGREE CONSTRAINED SPANNING
TREE, p. 206 (comment: "Remains NP-complete for any fixed K ≥ 2").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeFixedK

/-!
# DEGREE CONSTRAINED SPANNING TREE for fixed K ≥ 2 is NP-complete

For a fixed integer `K ≥ 2`:

INSTANCE: a graph `G = (V, E)`.
QUESTION: is there a spanning tree for `G` in which no vertex has degree larger than `K`?

This is DEGREE CONSTRAINED SPANNING TREE ([ND1], `DegreeConstrainedSpanningTreeWanted`) with the
degree bound `K` fixed instead of part of the instance. An instance is a graph `(n, E)`; it is
decided as the [ND1] instance `(n, E, K)` (`withBound K`), whose
`DegreeConstrainedSpanningTree.WellFormed` (`0 < n`, simple edge list) and
`DegreeConstrainedSpanningTree.DegreeConstrainedSpanningTreeFeasible` (a sublist of `n - 1`
edges forming a connected graph on `Fin n` in which no vertex meets `K + 1` of them) are reused
unchanged. `WellFormed` adds Garey and Johnson's instance bound `K ≤ |V|`, so graphs with fewer
than `K` vertices are no-instances. For `K = 2` the question is HAMILTONIAN PATH, the source of
the reduction.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`) and edge list; the bound `K` is fixed. -/
abbrev DegreeConstrainedSpanningTreeFixedKInstance := ℕ × List (ℕ × ℕ)

/-- The [ND1] instance `(n, E, K)` of a graph `(n, E)` and the fixed bound `K`. -/
def withBound (K : ℕ) (i : DegreeConstrainedSpanningTreeFixedKInstance) :
    DegreeConstrainedSpanningTree.DegreeConstrainedSpanningTreeInstance :=
  (i.1, i.2, K)

/-- Well-formedness of an instance for the fixed bound `K`: the [ND1] well-formedness of
`(n, E, K)` (`0 < n`, simple edge list) and Garey and Johnson's `K ≤ |V|`. -/
def WellFormed (K : ℕ) (i : DegreeConstrainedSpanningTreeFixedKInstance) : Prop :=
  DegreeConstrainedSpanningTree.WellFormed (withBound K i) ∧ K ≤ i.1

open Classical in
/-- DEGREE CONSTRAINED SPANNING TREE for a fixed bound `K` as a decision problem over
bitstrings. -/
noncomputable def degreeConstrainedSpanningTreeFixedKDec (K : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DegreeConstrainedSpanningTreeFixedKInstance) x with
  | some i => decide (WellFormed K i ∧
      DegreeConstrainedSpanningTree.DegreeConstrainedSpanningTreeFeasible (withBound K i))
  | none => false

/-- **DEGREE CONSTRAINED SPANNING TREE is NP-complete for every fixed `K ≥ 2`.** Source: Garey
and Johnson (1979), [ND1], comment. -/
public theorem_wanted degreeConstrainedSpanningTreeFixedK_npComplete (K : ℕ) (hK : 2 ≤ K) :
    degreeConstrainedSpanningTreeFixedKDec K ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (degreeConstrainedSpanningTreeFixedKDec K)

end MetaMathlibExt.Complexity.NPComplete.DegreeConstrainedSpanningTreeFixedK
