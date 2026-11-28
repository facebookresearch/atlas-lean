/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF B_k-VPG graphs (fixed k) is NP-complete

Source:
S. Chaplick, V. Jelínek, J. Kratochvíl and T. Vyskočil, "Bend-bounded path intersection graphs:
sausages, noodles, and waffles on a grill", WG 2012, Lecture Notes in Computer Science 7551
(2012), 274-285, doi:10.1007/978-3-642-34611-8_28.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BkVPGRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BkVPGRecognition

/-!
# RECOGNITION OF B_k-VPG graphs (fixed k) is NP-complete

Fix an integer `k ≥ 0`.
INSTANCE: a graph `G = (V, E)`.
QUESTION: is `G` a `B_k`-VPG graph, that is, the vertex intersection graph of paths with at
most `k` bends on a grid?

Chaplick, Jelínek, Kratochvíl and Vyskočil (2012, abstract): "A k-bend path is a path with at
most k 90 degree turns. The class of graphs representable by intersections of k-bend paths is
denoted by B_k-VPG. We show here that for every fixed k, ... recognition of graphs from B_k-VPG
is NP-complete even when the input graph is given by a B_{k+1}-VPG representation." This module
states the recognition problem for each fixed `k` (ISGCI classes "B_k-VPG", gc_1061, and its
instances `B_1`-, `B_2`-, `B_3`-VPG); `k` is not part of the instance.

The graph is simple and given by an edge list on `Fin n`; the path model is not part of the
input. A path on the grid is a nonempty list of grid points of `ℕ × ℕ` without repetitions in
which consecutive points are at distance `1` (they differ by `1` in exactly one coordinate),
i.e. a path in the grid graph; a single grid point is allowed. A bend is an inner point where
the path turns, that is, where a horizontal step (second coordinates equal) meets a vertical one
(no repeated point means no reversal, so every turn is a 90 degree turn). Two distinct vertices
are adjacent exactly when their paths share a grid point. Every finite model on the grid can be
translated into `ℕ × ℕ`. Paths of distinct vertices need not be distinct, as in
`WantedExt.Complexity.NPComplete.GraphColoringBZeroVPGWanted`. That module and
`WantedExt.Complexity.NPComplete.CliqueBOneVPGWanted` encode the cases `k = 0` and `k = 1` by
segments and by corner triples; lists of `k + 2` corners would also admit self-crossing curves
for `k ≥ 3`, so paths are given here as paths in the grid graph.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF B_k-VPG graphs is NP-complete for every fixed `k`.** Source: Chaplick,
Jelínek, Kratochvíl and Vyskočil (2012). -/
public theorem_wanted bkVPGRecognition_npComplete (k : ℕ) :
    bkVPGRecognitionDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (bkVPGRecognitionDec k)

end MetaMathlibExt.Complexity.NPComplete.BkVPGRecognition
