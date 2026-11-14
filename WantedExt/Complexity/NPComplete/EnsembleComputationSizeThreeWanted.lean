/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ENSEMBLE COMPUTATION with sets of size at most 3 is NP-complete

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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.EnsembleComputationWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EnsembleComputationSizeThree

open MetaMathlibExt.Complexity.NPComplete.EnsembleComputation
  (EnsembleComputationInstance EnsembleComputationFeasible)

/-!
# ENSEMBLE COMPUTATION with sets of size at most 3 is NP-complete

INSTANCE: a collection `C` of subsets of a finite set `A`, each `c ∈ C` with `|c| ≤ 3`, and a
positive integer `J`. QUESTION: is there a sequence `S = (z₁ ← x₁ ∪ y₁, ..., zⱼ ← xⱼ ∪ yⱼ)` of
`j ≤ J` union operations, where each `xᵢ` and `yᵢ` is either `{a}` for some `a ∈ A` or `zₖ`
for some `k < i`, such that `xᵢ` and `yᵢ` are disjoint, `1 ≤ i ≤ j`, and such that for every
subset `c ∈ C` there exists some `zᵢ`, `1 ≤ i ≤ j`, that is identical to `c`?

This is ENSEMBLE COMPUTATION (`WantedExt.Complexity.NPComplete.EnsembleComputationWanted`)
restricted to members of `C` with at most three elements. The instance type
`EnsembleComputationInstance` and the question `EnsembleComputationFeasible` are those of that
module, used directly; `WellFormed` is that module's well-formedness strengthened by the
restriction.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed ENSEMBLE COMPUTATION instance (every member of
`C` a strictly increasing list of elements of `A`, no member listed twice, `0 < J`) in which every
member of `C` has at most three elements. -/
def WellFormed (i : EnsembleComputationInstance) : Prop :=
  EnsembleComputation.WellFormed i ∧ ∀ c ∈ i.2.1, c.length ≤ 3

open Classical in
/-- ENSEMBLE COMPUTATION with sets of size at most 3 as a decision problem over bitstrings. -/
noncomputable def ensembleComputationSizeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EnsembleComputationInstance) x with
  | some i => decide (WellFormed i ∧ EnsembleComputationFeasible i)
  | none => false

/-- **ENSEMBLE COMPUTATION with sets of size at most 3 is NP-complete.** Source: Garey and Johnson (1979), [PO9], comment. -/
public theorem_wanted ensembleComputationSizeThree_npComplete :
    ensembleComputationSizeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ensembleComputationSizeThreeDec

end MetaMathlibExt.Complexity.NPComplete.EnsembleComputationSizeThree
