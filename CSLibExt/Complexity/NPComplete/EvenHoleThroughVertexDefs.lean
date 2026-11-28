/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# EVEN HOLE THROUGH A GIVEN VERTEX: definitions

Source:
D. Bienstock, "On the complexity of testing for odd holes and induced odd paths", Discrete
Mathematics 90 (1991), 85-92, doi:10.1016/0012-365X(91)90098-M, and "Corrigendum", Discrete
Mathematics 102 (1992), 109, doi:10.1016/0012-365X(92)90357-L;
H.-T. Cheong and H.-I. Lu, "Finding a shortest even hole in polynomial time", Journal of Graph
Theory 99 (2022), 425-434, doi:10.1002/jgt.22748 (arXiv:2008.06740; abstract: "Bienstock
[DM 1991 and 1992] proved that detecting an even (respectively, odd) hole containing a given
vertex is NP-complete").
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.OddHoleThroughVertexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EvenHoleThroughVertex

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, given vertex `v`, as in
`OddHoleThroughVertex`. -/
abbrev EvenHoleThroughVertexInstance := OddHoleThroughVertex.OddHoleThroughVertexInstance

/-- The graph has an even hole through `v`: an induced cycle `cycleGraph k ↪g G` of even length
`k ≥ 4` one of whose vertices is mapped to `v`. -/
def EvenHoleThroughVertexFeasible (i : EvenHoleThroughVertexInstance) : Prop :=
  ∃ k : ℕ, 4 ≤ k ∧ Even k ∧
    ∃ f : SimpleGraph.cycleGraph k ↪g OddHoleThroughVertex.Graph i,
      ∃ x, ((f x : Fin i.1) : ℕ) = i.2.2

open Classical in
/-- EVEN HOLE THROUGH A GIVEN VERTEX as a decision problem over bitstrings. -/
noncomputable def evenHoleThroughVertexDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EvenHoleThroughVertexInstance) x with
  | some i => decide (OddHoleThroughVertex.WellFormed i ∧ EvenHoleThroughVertexFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.EvenHoleThroughVertex
