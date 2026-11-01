/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Atteson's robustness theorem for neighbor joining

Neighbor joining is exact on tree metrics (`njRun_splits` in
`CSLibExt/Bioinformatics/Phylogenetics/NeighborJoining.lean`). Atteson (1999) proved that it
is also robust: if a dissimilarity `D` is within `μ / 2` of the path-length metric `d` of a
binary phylogenetic tree in the `ℓ∞` sense, where `μ` is the shortest internal edge length,
then every run of neighbor joining on `D` returns the topology of the tree. Atteson also
showed that the radius `1/2` cannot be improved.

The selection step is proved in
`CSLibExt/Bioinformatics/Phylogenetics/NeighborJoiningRobustness.lean`
(`exists_adj_adj_of_qCriterion_min_of_abs_sub_lt`: every Q-criterion minimizer of `D` is a
cherry). What remains is the induction over the run. The neighbor-joining update does not
preserve the `ℓ∞` bound in general (the new errors are only bounded by `3/2` times the old
bound), so a proof carries a weaker invariant; Mihaescu, Levy and
Pachter (2009) use quartet consistency and quartet additivity with respect to the tree, which
are linear in `D`, hold under the `ℓ∞` bound (their Corollary 20), are preserved by joining a
cherry (their Lemmas 17 and 18), and force the selected pair to be a cherry (their
Theorem 16).

Only internal edges enter the bound: Atteson states it with the shortest edge of the tree,
and the internal-edge form follows because lengthening the pendant edges of the tree and the
corresponding rows of `D` by a common amount does not change the pairs neighbor joining
selects (the shifting lemma, Mihaescu, Levy and Pachter 2009, Lemma 4). `NJRun` uses the
Studier–Keppler update `D (a ∪ b) c = (D a c + D b c - D a b) / 2`, which yields the same
topology as Saitou and Nei's averaging update (ibid., Corollary 5).

Sources: K. Atteson, "The performance of neighbor-joining methods of phylogenetic
reconstruction", Algorithmica 25 (1999) 251–278; R. Mihaescu, D. Levy and L. Pachter,
"Why neighbor-joining works", Algorithmica 54 (2009) 1–24.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Bioinformatics.Phylogenetics.NeighborJoining

@[expose] public section

namespace Cslib.Bioinformatics.Phylogenetics.NeighborJoiningRobustnessWanted

open Finset Cslib.Bioinformatics.Phylogenetics.NeighborJoining

/-- **Atteson's theorem: neighbor joining has `ℓ∞` radius `1/2`.** Let `d` be the path-length
metric of a binary phylogenetic `X`-tree `(G, ι)` with positive edge lengths `w`, let `μ` be a
lower bound on the lengths of its internal edges (edges with no taxon at either end), and let
`D` be a symmetric dissimilarity with zero diagonal such that `|D x y - d x y| < μ / 2` for
all distinct taxa. Then every complete run of neighbor joining on `D` (stopped with at most
three clusters) forms exactly the splits of the internal edges of the tree: a set of taxa `A`
or its complement is a formed cluster if and only if `A` is the set of taxa on the `a`-side of
an edge `{a, b}` with both endpoints internal.

Source: Atteson (1999); stated as Theorem 2 of Mihaescu, Levy and Pachter (2009), whose
Corollary 20 gives a proof. -/
theorem_wanted njRun_splits_of_abs_sub_lt {X : Type*} [DecidableEq X] [Fintype X] {V : Type*}
    [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] {ι : X → V}
    (hT : IsBinaryPhylogeneticTree G ι) {w : Sym2 V → ℝ} (hw : ∀ e ∈ G.edgeSet, 0 < w e)
    {d : X → X → ℝ}
    (hd : ∀ x y (p : G.Walk (ι x) (ι y)), p.IsPath → d x y = (p.edges.map w).sum)
    {μ : ℝ} (hμ : ∀ a b, G.Adj a b → a ∉ Set.range ι → b ∉ Set.range ι → μ ≤ w s(a, b))
    {D : X → X → ℝ} (hDsymm : ∀ x y, D x y = D y x) (hD0 : ∀ x, D x x = 0)
    (hDd : ∀ x y, x ≠ y → |D x y - d x y| < μ / 2)
    {S : Finset (Finset X)} {Dc : Finset X → Finset X → ℝ} {C : Finset (Finset X)}
    (hrun : NJRun D S Dc C) (hS : S.card ≤ 3) (A : Finset X) :
    (A ∈ C ∨ univ \ A ∈ C) ↔
      ∃ a b, G.Adj a b ∧ a ∉ Set.range ι ∧ b ∉ Set.range ι ∧
        ∀ x, x ∈ A ↔ (G.deleteEdges {s(a, b)}).Reachable (ι x) a

end Cslib.Bioinformatics.Phylogenetics.NeighborJoiningRobustnessWanted
