/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEASIBLE REGISTER ASSIGNMENT with out-degree at most 2 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 272, problem [PO2]
FEASIBLE REGISTER ASSIGNMENT (comment: remains NP-complete even if all vertices of `G` have
out-degree 2 or less);
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4
(1975), 226-248, doi:10.1137/0204020.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeasibleRegisterAssignmentWanted
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignmentOutDegreeAtMostTwo

/-!
# FEASIBLE REGISTER ASSIGNMENT with out-degree at most 2 is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which all vertices have out-degree 2 or less,
a positive integer `K`, and a register assignment `f : V → {R₁, R₂, ..., R_K}`. QUESTION: is
there a computation for `G` using the given register assignment, i.e., an ordering
`v₁, v₂, ..., vₙ` of `V` and a sequence `S₀, S₁, ..., Sₙ` of subsets of `V` that satisfies all
the properties given in REGISTER SUFFICIENCY and that in addition satisfies, for `1 ≤ j ≤ K`
and `1 ≤ i ≤ n`, there is at most one vertex `u ∈ Sᵢ` for which `f(u) = R_j`?

This is the restriction of `WantedExt.Complexity.NPComplete.FeasibleRegisterAssignmentWanted`
to digraphs of out-degree at most 2. The instance type, the digraph, the parent
well-formedness condition and the question are those of that module and of
`WantedExt.Complexity.NPComplete.RegisterSufficiencyWanted`
(`FeasibleRegisterAssignment.FeasibleRegisterAssignmentInstance`,
`FeasibleRegisterAssignment.toRegisterSufficiency`, `RegisterSufficiency.Graph`,
`FeasibleRegisterAssignment.WellFormed`,
`FeasibleRegisterAssignment.FeasibleRegisterAssignmentFeasible`). `WellFormed` adds the
restriction: every vertex `v` has at most two out-neighbors `u` (arcs `v → u`); the parent's
arc list has no repeated arcs, so this is the out-degree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: it is a well-formed FEASIBLE REGISTER ASSIGNMENT instance
(a directed acyclic graph, `K ≥ 1`, and a register index below `K` for each vertex), and every
vertex has out-degree at most 2. -/
def WellFormed (i : FeasibleRegisterAssignment.FeasibleRegisterAssignmentInstance) : Prop :=
  FeasibleRegisterAssignment.WellFormed i ∧
    ∀ v, {u | (RegisterSufficiency.Graph
      (FeasibleRegisterAssignment.toRegisterSufficiency i)).Adj v u}.ncard ≤ 2

open Classical in
/-- FEASIBLE REGISTER ASSIGNMENT with out-degree at most 2 as a decision problem over
bitstrings. -/
noncomputable def feasibleRegisterAssignmentOutDegreeAtMostTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeasibleRegisterAssignment.FeasibleRegisterAssignmentInstance) x with
  | some i =>
    decide (WellFormed i ∧ FeasibleRegisterAssignment.FeasibleRegisterAssignmentFeasible i)
  | none => false

/-- **FEASIBLE REGISTER ASSIGNMENT is NP-complete for out-degree at most 2.** Source: Garey and
Johnson (1979), [PO2]; Sethi (1975). -/
public theorem_wanted feasibleRegisterAssignmentOutDegreeAtMostTwo_npComplete :
    feasibleRegisterAssignmentOutDegreeAtMostTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feasibleRegisterAssignmentOutDegreeAtMostTwoDec

end MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignmentOutDegreeAtMostTwo
