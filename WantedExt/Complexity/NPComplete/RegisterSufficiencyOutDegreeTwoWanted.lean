/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# REGISTER SUFFICIENCY (out-degree at most 2) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO1] REGISTER
SUFFICIENCY (comment: remains NP-complete even if all vertices of `G` have
out-degree 2 or less);
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4
(1975), 226-248, doi:10.1137/0204020.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RegisterSufficiencyWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyOutDegreeTwo

/-!
# REGISTER SUFFICIENCY (out-degree at most 2) is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)` in which every vertex has out-degree at most
`2`, and a positive integer `K`. QUESTION: is there a computation for `G` that uses `K` or
fewer registers, i.e., an ordering `v₁, …, vₙ` of the vertices in `V`, where `n = |V|`, and a
sequence `S₀, …, Sₙ` of subsets of `V`, each satisfying `|Sᵢ| ≤ K`, such that `S₀` is empty,
`Sₙ` contains all vertices with in-degree `0` in `G`, and, for `1 ≤ i ≤ n`, `vᵢ ∈ Sᵢ`,
`Sᵢ - {vᵢ} ⊆ Sᵢ₋₁`, and `Sᵢ₋₁` contains all vertices `u` for which `(vᵢ, u) ∈ A`?

This is REGISTER SUFFICIENCY (`MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency`)
restricted to digraphs of out-degree at most `2` (every vertex has at most two operands); the
instance type, the digraph, the well-formedness conditions and the question are reused from
that module unchanged. The arc list has no repeated arcs (parent `WellFormed`), so the
out-degree of `v` is the number of arcs `(v, u)` in the list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed REGISTER SUFFICIENCY instance in which every
vertex is the tail of at most two arcs. -/
def WellFormed (i : RegisterSufficiency.RegisterSufficiencyInstance) : Prop :=
  RegisterSufficiency.WellFormed i ∧ ∀ a ∈ i.2.1, i.2.1.countP (fun b => b.1 = a.1) ≤ 2

open Classical in
/-- REGISTER SUFFICIENCY (out-degree at most 2) as a decision problem over bitstrings. -/
noncomputable def registerSufficiencyOutDegreeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RegisterSufficiency.RegisterSufficiencyInstance) x with
  | some i => decide (WellFormed i ∧ RegisterSufficiency.RegisterSufficiencyFeasible i)
  | none => false

/-- **REGISTER SUFFICIENCY (out-degree at most 2) is NP-complete.** Source: Garey and Johnson
(1979), [PO1]; Sethi (1975). -/
public theorem_wanted registerSufficiencyOutDegreeTwo_npComplete :
    registerSufficiencyOutDegreeTwoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L registerSufficiencyOutDegreeTwoDec

end MetaMathlibExt.Complexity.NPComplete.RegisterSufficiencyOutDegreeTwo
