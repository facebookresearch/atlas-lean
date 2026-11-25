/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Matching.ShortAugmentingPath

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

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

open scoped symmDiff

/-- **Disjoint augmenting paths in a symmetric difference (Hopcroft–Karp, Theorem 1).** Let `M`
and `N` be matchings of a finite simple graph `G`. Then there are `|N| - |M|` pairwise
vertex-disjoint `M`-augmenting walks whose edges all lie in `M ⊕ N` (Hopcroft and Karp, SIAM J.
Comput. 2 (1973), §2, Theorem 1, stated there for `|N| > |M|`; when `|N| ≤ |M|` the truncated
difference is `0` and the statement is empty). -/
theorem_wanted exists_disjoint_augmentingWalks {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (M N : Finset (Sym2 V))
    (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    (hNG : ∀ e ∈ N, e ∈ G.edgeSet)
    (hN : ∀ e₁ ∈ N, ∀ e₂ ∈ N, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂) :
    ∃ P : Fin (N.card - M.card) → (u : V) × (v : V) × G.Walk u v,
      (∀ i, IsAugmentingWalk M (P i).2.2 ∧ ∀ e ∈ (P i).2.2.edges, e ∈ M ∆ N) ∧
        ∀ i j, i ≠ j → List.Disjoint (P i).2.2.support (P j).2.2.support

/-- **Augmenting after a shortest augmentation (Hopcroft–Karp, Theorem 2).** Let `M` be a matching
of a finite simple graph `G`, `p` a shortest `M`-augmenting walk, and `q` a walk augmenting for
the matching `M ⊕ E(p)` obtained by augmenting along `p`. Then
`|q| ≥ |p| + |E(p) ∩ E(q)|` (Hopcroft and Karp, SIAM J. Comput. 2 (1973), §2, Theorem 2). -/
theorem_wanted IsAugmentingWalk.length_add_card_inter_le {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (M : Finset (Sym2 V))
    (hMG : ∀ e ∈ M, e ∈ G.edgeSet)
    (hM : ∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → ∀ v : V, v ∈ e₁ → v ∉ e₂)
    {u v : V} (p : G.Walk u v) (hp : IsAugmentingWalk M p)
    (hshort : ∀ (u' v' : V) (p' : G.Walk u' v'), IsAugmentingWalk M p' → p.length ≤ p'.length)
    {u' v' : V} (q : G.Walk u' v') (hq : IsAugmentingWalk (M ∆ p.edges.toFinset) q) :
    p.length + (p.edges.toFinset ∩ q.edges.toFinset).card ≤ q.length

end MetaMathlibExt
