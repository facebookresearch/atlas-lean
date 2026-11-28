/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENSEMBLE COMPUTATION without disjointness, with sets of size at most 3 is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [PO9] ENSEMBLE COMPUTATION, comment
("Remains NP-complete even if each `c ∈ C` satisfies `|c| ≤ 3`. The analogous problem in which
`xᵢ` and `yᵢ` need not be disjoint for `1 ≤ i ≤ j` is also NP-complete under the same
restriction"); the entry's reference is "[Garey and Johnson, ——]. Transformation from VERTEX
COVER (see Section 3.2.2)", the book's Theorem 3.6.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EnsembleComputationNonDisjointDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputationNonDisjoint

open MetaMathlibExt.Complexity.NPComplete.EnsembleComputation
  (EnsembleComputationInstance toSubset operandValue)

/-!
# ENSEMBLE COMPUTATION without disjointness, with sets of size at most 3 is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `A`, each `c ∈ C` with `|c| ≤ 3`, and a
positive integer `J`. QUESTION: is there a sequence `S = (z₁ ← x₁ ∪ y₁, ..., zⱼ ← xⱼ ∪ yⱼ)` of
`j ≤ J` union operations, where each `xᵢ` and `yᵢ` is either `{a}` for some `a ∈ A` or `zₖ`
for some `k < i`, such that for every subset `c ∈ C` there exists some `zᵢ`, `1 ≤ i ≤ j`, that is
identical to `c`? Unlike ENSEMBLE COMPUTATION, `xᵢ` and `yᵢ` need not be disjoint.

The instance type `EnsembleComputationInstance`, `toSubset` and `operandValue` are those of
ENSEMBLE COMPUTATION (`WantedExt.Complexity.NPComplete.EnsembleComputationWanted`), used
directly; `WellFormed` is that module's well-formedness strengthened by the restriction
`|c| ≤ 3`; the question is that module's `EnsembleComputationFeasible` without its disjointness
conjunct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ENSEMBLE COMPUTATION without disjointness, with sets of size at most 3 is NP-complete.** Source: Garey and Johnson (1979), [PO9], comment. -/
public theorem_wanted ensembleComputationNonDisjoint_npComplete :
    ensembleComputationNonDisjointDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ensembleComputationNonDisjointDec

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputationNonDisjoint
