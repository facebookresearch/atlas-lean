/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMUM COMMUNICATION SPANNING TREE with equal requirements: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND7] OPTIMUM COMMUNICATION
SPANNING TREE (p. 207), comment "Remains NP-complete even if all requirements are equal";
D. S. Johnson, J. K. Lenstra and A. H. G. Rinnooy Kan, "The complexity of the network design
problem", Networks 8(4) (1978), 279-285, doi:10.1002/net.3230080402.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeEqualRequirements

open MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTree

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

end MetaMathlibExt.Complexity.NPComplete.OptimumCommunicationSpanningTreeEqualRequirements
