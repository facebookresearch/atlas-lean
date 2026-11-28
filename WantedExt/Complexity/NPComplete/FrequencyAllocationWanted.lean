/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FREQUENCY ALLOCATION is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
problem MAXIMUM FREQUENCY ALLOCATION;
E. Malesińska and A. Panconesi, "On the hardness of allocating frequencies for hybrid networks",
Theoret. Comput. Sci. 209 (1998), 347-363, doi:10.1016/S0304-3975(98)00156-X (the channel
stability number; Section 1: the problem generalizes list coloring);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT4] GRAPH K-COLORABILITY.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.FrequencyAllocationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FrequencyAllocation

/-!
# FREQUENCY ALLOCATION is NP-complete

INSTANCE: a graph `G = (V, E)`, for each node `u` a finite set `L(u) ⊂ ℤ⁺` of available
frequencies and an integer `M_u`, and a positive integer `K`.
QUESTION: is there a frequency allocation for `G`, i.e., for each node `u` a subset `S(u)` of
`L(u)` with `1 ≤ |S(u)| ≤ M_u`, such that `S(u) ∩ S(v) = ∅` for all `(u, v) ∈ E`, whose stability
number `∑_{u ∈ V} |S(u)|` is at least `K`?

This is the decision version of MAXIMUM FREQUENCY ALLOCATION (an entry of the Crescenzi-Kann
compendium), a form of the channel stability number of Malesińska and Panconesi without their
co-site constraints. The bound is a positive integer, following the Garey-Johnson convention for
decision versions. NP-hardness: with `M_u = 1` for every node and `K = |V|`, an allocation is a
choice of one frequency per node from its list, different at adjacent nodes, i.e., a list
coloring (`WantedExt.Complexity.NPComplete.ListColoringWanted`); with every list `{1, …, k}`
this is GRAPH K-COLORABILITY [GT4].

The graph has nodes `0, …, n - 1` and is given by a list of distinct undirected edges without
loops or repeated pairs; the lists of available frequencies are the `n` lists of a
`ListColoringWanted` instance, whose well-formedness is reused, and here they additionally have
distinct positive entries. The allocation gives each node a list of distinct frequencies taken
from its list, so `|S(u)|` is that list's length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **FREQUENCY ALLOCATION is NP-complete.** Source: Crescenzi and Kann, MAXIMUM FREQUENCY
ALLOCATION; Malesińska and Panconesi (1998); Garey and Johnson (1979), [GT4]. -/
public theorem_wanted frequencyAllocation_npComplete :
    frequencyAllocationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L frequencyAllocationDec

end MetaMathlibExt.Complexity.NPComplete.FrequencyAllocation
