/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROUTING WITH MUST PAIRS: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide" (fifth edition), Journal of
Algorithms 3 (1982), 381-395, doi:10.1016/0196-6774(82)90032-3, problem [2] ROUTING WITH
"MUST PAIRS" (reference: Ntafos and Hakimi; transformation from 3SAT);
S. C. Ntafos and S. L. Hakimi, "On path cover problems in digraphs and applications to
program testing", IEEE Transactions on Software Engineering SE-5 (1979), 520-529,
doi:10.1109/TSE.1979.234213.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Relation
public import CSLibExt.Complexity.NPComplete.PathWithForbiddenPairsDefs
public import CSLibExt.Complexity.NPComplete.DirectedTwoDisjointConnectingPathsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RoutingWithMustPairs

/-- Well-formedness of an instance: the parent's (arcs, `s`, `t` and must-pairs use vertices
below `n`), the digraph is acyclic, and every must-pair `(u, v)` is in the transitive closure
of the arcs. -/
def WellFormed (i : PathWithForbiddenPairs.PathWithForbiddenPairsInstance) : Prop :=
  PathWithForbiddenPairs.WellFormed i ∧
    (∀ v, ¬ Relation.TransGen (fun u w => (u, w) ∈ i.2.1) v v) ∧
    ∀ m ∈ i.2.2.2.2, Relation.TransGen (fun u w => (u, w) ∈ i.2.1) m.1 m.2

/-- Some path `P` from `s` to `t` passes through `v` whenever it passes through `u`, for every
must-pair `(u, v)`. -/
def RoutingWithMustPairsFeasible
    (i : PathWithForbiddenPairs.PathWithForbiddenPairsInstance) : Prop :=
  ∃ p : List ℕ, DirectedTwoDisjointConnectingPaths.IsDirectedPath i.2.1 i.2.2.1 i.2.2.2.1 p ∧
    ∀ m ∈ i.2.2.2.2, m.1 ∈ p → m.2 ∈ p

open Classical in
/-- ROUTING WITH MUST PAIRS as a decision problem over bitstrings. -/
noncomputable def routingWithMustPairsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathWithForbiddenPairs.PathWithForbiddenPairsInstance) x with
  | some i => decide (WellFormed i ∧ RoutingWithMustPairsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RoutingWithMustPairs
