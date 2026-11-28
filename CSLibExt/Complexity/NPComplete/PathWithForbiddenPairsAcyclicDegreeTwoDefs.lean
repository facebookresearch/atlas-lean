/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATH WITH FORBIDDEN PAIRS on acyclic digraphs of in- and out-degree at most 2: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT54] PATH WITH FORBIDDEN PAIRS,
p. 203 (comment: "Remains NP-complete even if `G` is acyclic with no in- or out-degree
exceeding 2.");
H. N. Gabow, S. N. Maheshwari and L. J. Osterweil, "On two problems in the generation of
program test paths", IEEE Transactions on Software Engineering SE-2 (1976), 227-231,
doi:10.1109/TSE.1976.233819.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import Mathlib.Data.Finset.Card
public import CSLibExt.Complexity.NPComplete.PathWithForbiddenPairsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsAcyclicDegreeTwo

/-- Well-formedness of an instance: the parent's (arcs, `s`, `t` and pairs use vertices below
`m`), the digraph is acyclic, and every vertex has at most 2 distinct in-neighbours and at most
2 distinct out-neighbours. -/
def WellFormed (i : PathWithForbiddenPairs.PathWithForbiddenPairsInstance) : Prop :=
  PathWithForbiddenPairs.WellFormed i ∧
    (∀ v, ¬ Relation.TransGen (fun u w => (u, w) ∈ i.2.1) v v) ∧
    ∀ v, ((Finset.range i.1).filter fun u => (u, v) ∈ i.2.1).card ≤ 2 ∧
      ((Finset.range i.1).filter fun w => (v, w) ∈ i.2.1).card ≤ 2

open Classical in
/-- PATH WITH FORBIDDEN PAIRS on acyclic digraphs of in- and out-degree at most 2, as a
decision problem over bitstrings. -/
noncomputable def pathWithForbiddenPairsAcyclicDegreeTwoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathWithForbiddenPairs.PathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ PathWithForbiddenPairs.PathWithForbiddenPairsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PathWithForbiddenPairsAcyclicDegreeTwo
