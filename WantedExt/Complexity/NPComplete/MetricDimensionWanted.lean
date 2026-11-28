/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC DIMENSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT61] METRIC
DIMENSION (an unpublished result of the authors);
S. Khuller, B. Raghavachari, and A. Rosenfeld, "Landmarks in graphs",
Discrete Applied Mathematics 70 (1996), 217-229,
doi:10.1016/0166-218X(95)00106-2 (a published proof).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MetricDimensionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricDimension

/-!
# METRIC DIMENSION is NP-complete

INSTANCE: a connected graph `G = (V, E)` and a positive integer `K ≤ |V|`. QUESTION: is there a
subset `V' ⊆ V` with `|V'| ≤ K` such that for each pair `u, v` of distinct vertices there is a
vertex `w ∈ V'` with `d(u, w) ≠ d(w, v)`? Such a `V'` is a resolving set (a set of landmarks).

The distance `d` is Mathlib's `SimpleGraph.dist`, the length of a shortest walk; it is the
graph distance because `WellFormed` requires `G` to be connected (Mathlib's `dist` is `0` for
unreachable pairs, and the metric dimension is defined for connected graphs).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **METRIC DIMENSION is NP-complete.** Source: Garey and Johnson (1979), [GT61]; Khuller,
Raghavachari, and Rosenfeld (1996). -/
public theorem_wanted metricDimension_npComplete :
    metricDimensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L metricDimensionDec

end MetaMathlibExt.Complexity.NPComplete.MetricDimension
