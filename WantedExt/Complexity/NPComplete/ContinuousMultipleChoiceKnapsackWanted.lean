/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CONTINUOUS MULTIPLE CHOICE KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP11] CONTINUOUS
MULTIPLE CHOICE KNAPSACK;
T. Ibaraki, "Approximate algorithms for the multiple-choice continuous knapsack
problems", Journal of the Operations Research Society of Japan 23 (1980), 28-63,
doi:10.15807/jorsj.23.28.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsack

/-!
# CONTINUOUS MULTIPLE CHOICE KNAPSACK is NP-complete

INSTANCE: a finite set `U`, for each `u ∈ U` a size `s(u) ∈ ℤ⁺` and a value `v(u) ∈ ℤ⁺`, a
partition of `U` into disjoint sets `U₁, U₂, …, Uₘ`, and positive integers `B` and `K`.
QUESTION: is there a choice of a unique element `uᵢ ∈ Uᵢ`, `1 ≤ i ≤ m`, and an assignment of
rational numbers `rᵢ`, `0 ≤ rᵢ ≤ 1`, to these elements, such that `∑ rᵢ s(uᵢ) ≤ B` and
`∑ rᵢ v(uᵢ) ≥ K`?

The partition is given block by block: a list of `m` nonempty lists, block `Uᵢ` listing its
elements as (size, value) pairs. The choice is a list with one entry from each block, in block
order (`List.Forall₂ (· ∈ ·)`, the shape of CSLibExt's
`Cslib.Algorithms.Lean.MultipleChoiceKnapsack.IsSelection`), and `rᵢ` is the `i`-th entry of a
list of rationals of the same length. The problem is NP-complete in the ordinary sense for the
binary encoding of the numbers (it is solvable in pseudo-polynomial time).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CONTINUOUS MULTIPLE CHOICE KNAPSACK is NP-complete.** Source: Garey and Johnson (1979),
[MP11]; Ibaraki (1980). -/
public theorem_wanted continuousMultipleChoiceKnapsack_npComplete :
    continuousMultipleChoiceKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L continuousMultipleChoiceKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.ContinuousMultipleChoiceKnapsack
