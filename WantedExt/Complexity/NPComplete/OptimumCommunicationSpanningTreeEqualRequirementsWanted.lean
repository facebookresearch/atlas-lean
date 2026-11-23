/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMUM COMMUNICATION SPANNING TREE with equal requirements is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND7] OPTIMUM COMMUNICATION
SPANNING TREE (p. 207), comment "Remains NP-complete even if all requirements are equal";
D. S. Johnson, J. K. Lenstra and A. H. G. Rinnooy Kan, "The complexity of the network design
problem", Networks 8(4) (1978), 279-285, doi:10.1002/net.3230080402.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeEqualRequirements

open MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTree

/-!
# OPTIMUM COMMUNICATION SPANNING TREE with equal requirements is NP-complete

INSTANCE: a complete graph `G = (V, E)`, a weight `w(e) ∈ ℤ₀⁺` for each `e ∈ E`, a requirement
`r({u, v}) ∈ ℤ₀⁺` for each pair `{u, v}` of vertices from `V`, all requirements equal, and a
bound `B ∈ ℤ₀⁺`. QUESTION: is there a spanning tree `T` for `G` such that, if `W({u, v})`
denotes the sum of the weights of the edges on the path joining `u` and `v` in `T`, then
`∑_{u, v ∈ V} W({u, v}) · r({u, v}) ≤ B`?

This is the restriction of OPTIMUM COMMUNICATION SPANNING TREE ([ND7],
`OptimumCommunicationSpanningTreeWanted`) to instances in which every pair of distinct vertices
has the same requirement. The instance type, `OptimumCommunicationSpanningTree.WellFormed`
(symmetric weight and requirement matrices with zero diagonal, at least one vertex) and
`OptimumCommunicationSpanningTree.OptimumCommunicationSpanningTreeFeasible` (the sum over
unordered pairs of distinct vertices) are the parent's, unchanged; `WellFormed` adds that all
off-diagonal requirements equal one common value. Garey and Johnson record that the problem is
solvable in polynomial time if all edge weights are equal (Hu, 1974).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the parent's (at least one vertex; symmetric weight and
requirement matrices with zero diagonal), and some `c` is the requirement of every pair of
distinct vertices. -/
def WellFormed (i : OptimumCommunicationSpanningTreeInstance) : Prop :=
  OptimumCommunicationSpanningTree.WellFormed i ∧
    ∃ c : ℕ, ∀ u v : Fin i.1, u ≠ v → requirement i u v = c

open Classical in
/-- OPTIMUM COMMUNICATION SPANNING TREE with equal requirements as a decision problem over
bitstrings. -/
noncomputable def optimumCommunicationSpanningTreeEqualRequirementsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimumCommunicationSpanningTreeInstance) x with
  | some i => decide (WellFormed i ∧ OptimumCommunicationSpanningTreeFeasible i)
  | none => false

/-- **OPTIMUM COMMUNICATION SPANNING TREE is NP-complete with equal requirements.** Source:
Garey and Johnson (1979), [ND7], comment; Johnson, Lenstra and Rinnooy Kan (1978). -/
public theorem_wanted optimumCommunicationSpanningTreeEqualRequirements_npComplete :
    optimumCommunicationSpanningTreeEqualRequirementsDec ∈
        MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L optimumCommunicationSpanningTreeEqualRequirementsDec

end MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeEqualRequirements
