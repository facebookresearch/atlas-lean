/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM EQUIVALENT DIGRAPH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), MINIMUM EQUIVALENT
DIGRAPH; A. V. Aho, M. R. Garey, and J. D. Ullman, "The transitive reduction of a directed
graph", SIAM Journal on Computing 1 (1972), 131-137 (distinguishing transitive reduction from
the minimum equivalent subgraph and the hardness connection); D. M. Moyles and G. L. Thompson,
"An algorithm for finding a minimum equivalent graph of a digraph", Journal of the ACM 16
(1969), 455-460.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph

/-!
# MINIMUM EQUIVALENT DIGRAPH is NP-complete

A directed graph and a bound `K`. The question is whether some spanning subdigraph with at most
`K` arcs has exactly the same reachability relation: two vertices are joined by a directed path
in the subdigraph iff they are in the original. Reachability is witnessed by paths of length at
most `n + 1`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound. -/
abbrev MinimumEquivalentDigraphInstance := ℕ × List (ℕ × ℕ) × ℕ


/-- Directed adjacency from an edge list (as a Bool, for use in filters). -/
def DAdj (edges : List (ℕ × ℕ)) (u v : ℕ) : Bool :=
  edges.contains (u, v)

/-- Reachability by a directed path of length at most `n + 1`. -/
def Reachable (n : ℕ) (E : List (ℕ × ℕ)) (u v : ℕ) : Prop :=
  ∃ path : List ℕ, path.length ≤ n + 1 ∧ path ≠ [] ∧
    path.getD 0 0 = u ∧ path.getD (path.length - 1) 0 = v ∧
    ∀ j, j + 1 < path.length → DAdj E (path.getD j 0) (path.getD (j + 1) 0)


/-- Well-formedness of an instance. -/
def WellFormed (i : MinimumEquivalentDigraphInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2

/-- A spanning subdigraph with at most `K` arcs and the same reachability. -/
def MinimumEquivalentDigraphFeasible
    (i : MinimumEquivalentDigraphInstance) : Prop :=
  ∃ F : List (ℕ × ℕ), F.Sublist i.2.1 ∧ F.length ≤ i.2.2 ∧
    ∀ u < i.1, ∀ v < i.1, Reachable i.1 i.2.1 u v ↔ Reachable i.1 F u v

open Classical in
/-- MINIMUM EQUIVALENT DIGRAPH as a decision problem over bitstrings. -/
noncomputable def minimumEquivalentDigraphDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumEquivalentDigraphInstance) x with
  | some i => decide (WellFormed i ∧ MinimumEquivalentDigraphFeasible i)
  | none => false

/-- **MINIMUM EQUIVALENT DIGRAPH is NP-complete.** Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), MINIMUM EQUIVALENT DIGRAPH; A. V. Aho, M. R. Garey,
and J. D. Ullman, "The transitive reduction of a directed graph", SIAM Journal on
Computing 1 (1972), 131-137 (distinguishing transitive reduction from the minimum
equivalent subgraph and the hardness connection); D. M. Moyles and G. L. Thompson, "An
algorithm for finding a minimum equivalent graph of a digraph", Journal of the ACM 16
(1969), 455-460. -/
public theorem_wanted minimumEquivalentDigraph_npComplete :
    minimumEquivalentDigraphDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumEquivalentDigraphDec

end MetaMathlibExt.Complexity.NPComplete.MinimumEquivalentDigraph
