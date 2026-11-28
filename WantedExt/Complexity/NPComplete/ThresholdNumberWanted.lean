/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# THRESHOLD NUMBER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT63] THRESHOLD
NUMBER;
V. Chvátal and P. L. Hammer, "Aggregation of inequalities in integer
programming", Annals of Discrete Mathematics 1 (1977), 145-162,
doi:10.1016/S0167-5060(08)70731-3 (threshold graphs and the threshold number);
M. Yannakakis, "The complexity of the partial order dimension problem", SIAM
Journal on Algebraic and Discrete Methods 3 (1982), 351-358,
doi:10.1137/0603036 (NP-complete for every fixed `K ≥ 3`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ThresholdNumberDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ThresholdNumber

/-!
# THRESHOLD NUMBER is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: are there `k ≤ K`
subsets `E₁, ..., Eₖ` of `E`, with union `E`, such that each graph `(V, Eᵢ)` is a threshold
graph?

A graph on `n` vertices is a threshold graph (Chvátal and Hammer) if there are real numbers
`a₁, ..., aₙ` and `b` such that the zero-one solutions of `∑ aᵢ xᵢ ≤ b` are the characteristic
vectors of the cliques of the graph (`IsThresholdGraph`; the vertex sets `S` play the role of
the zero-one vectors). Each `(V, Eᵢ)` is a graph `H j` on all of `V` with `H j ≤ G`; the union of
the edge sets is `E` when every edge of `G` is an edge of some `H j`. Empty `Eᵢ` are harmless
because the bound is `k ≤ K`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **THRESHOLD NUMBER is NP-complete.** Source: Garey and Johnson (1979), [GT63]; Chvátal and
Hammer (1977); Yannakakis (1982). -/
public theorem_wanted thresholdNumber_npComplete :
    thresholdNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L thresholdNumberDec

end MetaMathlibExt.Complexity.NPComplete.ThresholdNumber
