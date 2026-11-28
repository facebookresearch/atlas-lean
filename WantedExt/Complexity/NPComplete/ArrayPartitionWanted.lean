/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ARRAY PARTITION is NP-complete

Source:
M. Grigni and F. Manne, "On the complexity of the generalized block distribution", in *Parallel
Algorithms for Irregularly Structured Problems (IRREGULAR '96)*, Lecture Notes in Computer
Science 1117, Springer (1996), 319-326, doi:10.1007/BFb0030123, Theorem 2 ("GBD is
NP-Complete"; the reduction from BALANCED COMPLETE BIPARTITE SUBGRAPH builds a square zero-one
array with `p = q` and `K = 1`, and the conclusion notes that GBD "remains NP-complete for any
derived cost function such as the sum of the elements in a block");
P. Crescenzi and V. Kann, *A compendium of NP optimization problems* (2000), problem
MINIMUM ARRAY PARTITION.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ArrayPartitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ArrayPartition

/-!
# ARRAY PARTITION is NP-complete

INSTANCE: an `n × n` array `A` of non-negative integers, a positive integer `p`, and a
non-negative integer `K`.
QUESTION: are there `p - 1` horizontal dividers `0 = h_0 < h_1 < ⋯ < h_p = n` and `p - 1`
vertical dividers `0 = v_0 < v_1 < ⋯ < v_p = n`, partitioning `A` into `p²` blocks, such that
the sum of the entries of every block is at most `K`?

This is the decision version of the compendium's MINIMUM ARRAY PARTITION, the generalized block
distribution of Grigni and Manne with `p = q` and the sum of the entries as the cost of a block.
Block `(i, j)` consists of the rows `r` with `h_i ≤ r < h_{i+1}` and the columns `c` with
`v_j ≤ c < v_{j+1}` (rows and columns indexed from `0`, so the compendium's `h_{j-1} < y ≤ h_j`
becomes `h_j ≤ r < h_{j+1}`). Grigni and Manne allow empty intervals (`h_i ≤ h_{i+1}`); with
non-negative entries splitting a block never increases a block sum, so when `p ≤ n` any
distribution with empty intervals can be refined to one with `p` nonempty intervals of no larger
cost, and the strict dividers of the compendium give the same problem on the instances of their
reduction, which have `p ≤ n` (for `p > n` there are no strict dividers, a no-instance). Their
reduction uses a zero-one array, so the problem is NP-complete in the strong
sense; the entries are written in binary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **ARRAY PARTITION is NP-complete.** Source: Grigni and Manne (1996), Theorem 2; Crescenzi and
Kann, MINIMUM ARRAY PARTITION. -/
public theorem_wanted arrayPartition_npComplete :
    arrayPartitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L arrayPartitionDec

end MetaMathlibExt.Complexity.NPComplete.ArrayPartition
