/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 3-PARTITION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), 3-PARTITION (strongly NP-
complete).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThreePartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThreePartition

/-!
# 3-PARTITION is NP-complete

A list of `3m` natural numbers and a target `B`. The question is whether the numbers can be
split into `m` triples each summing to `B`. The usual `B / 4 < a < B / 2` promise is not needed
when the triple size is explicit.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **3-PARTITION is NP-complete.** The decision problem 3-PARTITION on bitstrings is in NP, and
every decision problem in NP reduces to it by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), 3-PARTITION (strongly NP-complete). -/
public theorem_wanted threePartition_npComplete :
    threePartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L threePartitionDec

end MetaMathlibExt.Complexity.NPComplete.ThreePartition
