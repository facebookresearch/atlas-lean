/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Matching.ShortAugmentingPath
public import MathlibExt.Combinatorics.HopcroftKarpAugmentingPathsLengthAddCardInterLe

/-!
# Hopcroft and Karp's augmenting-path lemmas in general graphs

Hopcroft and Karp, *An n^{5/2} algorithm for maximum matchings in bipartite graphs*, SIAM J.
Comput. 2(4) (1973) 225–231, §2, derive their phase bound from three facts about matchings in an
arbitrary finite graph (their §2 is written for general graphs with the nonbipartite case in
view):

* Theorem 1: if `|N| > |M|`, the symmetric difference `M ⊕ N` contains `|N| - |M|`
  vertex-disjoint `M`-augmenting paths;
* Corollary 2: hence an `M`-augmenting path of length at most `2 ⌊r / (s - r)⌋ + 1` exists, where
  `r = |M| < s`;
* Theorem 2: if `P` is a shortest `M`-augmenting path and `P'` is augmenting for `M ⊕ P`, then
  `|P'| ≥ |P| + |P ∩ P'|`.

Their Lemma 1 (`MetaMathlibExt.IsAugmentingWalk.symmDiff_isMatching`) and Corollary 1, Berge's
lemma (`MetaMathlibExt.berge_iff_not_exists_isAugmentingWalk`), are proved. The bipartite
algorithm built on these facts is proved correct, with the `2 ⌊√b⌋ + 2` phase bound, in
`CSLibExt.Algorithms.Lean.Graph.BipartiteMatching`, where the counting step uses vertex covers
instead of Theorem 1.

Matchings are finite edge sets as in `MetaMathlibExt.Berge`, and paths are walks satisfying
`MetaMathlibExt.IsAugmentingWalk`; path lengths count edges.
-/
