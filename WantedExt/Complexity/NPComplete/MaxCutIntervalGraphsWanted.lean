/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAX CUT on interval graphs is NP-complete

Source:
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70(2) (2023), 307-322, doi:10.1007/s00454-022-00472-y
(SoCG 2021; preprint arXiv:2006.00061).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MaxCutIntervalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MaxCutIntervalGraphs

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)
open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion (IsIntervalGraph)

/-!
# MAX CUT on interval graphs is NP-complete

INSTANCE: an interval graph `G = (V, E)` (simple, undirected) and an integer `k` with
`1 ≤ k ≤ |E|`. QUESTION: does `G` have a cut of size at least `k`, i.e. a partition of `V` into
`A` and `B` with at least `k` edges between `A` and `B`? (Adhikary, Bose, Mukherjee and Roy,
Section 2, decision version of Max Cut; Theorem 1: Max Cut is NP-complete on interval graphs.)

The instance, the simple-edge-list conditions, and the question are those of MAXIMUM CUT
(`CSLibExt.Complexity.NPComplete.MaxCutDefs`, whose question counts edges), reused here as
in `SimpleMaxCutDegreeThreeWanted`. An interval graph is the intersection graph of closed
intervals on the real line, the repository's `IntervalGraphCompletion.IsIntervalGraph` (also
used by `AchromaticNumberIntervalGraphsWanted`), applied to `Cslib.Complexity.Karp.edgeGraph`.
The edge list has no repeated edge, so `|E|` is its length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MAX CUT on interval graphs is NP-complete.** Source: Adhikary, Bose, Mukherjee and Roy
(2023). -/
public theorem_wanted maxCutIntervalGraphs_npComplete :
    maxCutIntervalGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L maxCutIntervalGraphsDec

end MetaMathlibExt.Complexity.NPComplete.MaxCutIntervalGraphs
