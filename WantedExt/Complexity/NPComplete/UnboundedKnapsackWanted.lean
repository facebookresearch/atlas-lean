/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNBOUNDED KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), UNBOUNDED KNAPSACK.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.UnboundedKnapsackDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnboundedKnapsack

/-!
# UNBOUNDED KNAPSACK is NP-complete

Items with weights and values, a capacity, and a target value, with each item reusable any
number of times. The question is whether multiplicities (a list of natural numbers, binary-
sized) achieve total weight at most the capacity and total value at least the target.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **UNBOUNDED KNAPSACK is NP-complete.** The unbounded knapsack decision problem belongs to NP,
and every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), UNBOUNDED KNAPSACK. -/
public theorem_wanted unboundedKnapsack_npComplete :
    unboundedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unboundedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.UnboundedKnapsack
