/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Tree bisection and reconnection distance equals the maximum agreement forest number

Allen and Steel (2001, Definition 2.3): a tree bisection and reconnection (TBR) on an unrooted
binary phylogenetic tree `T` removes an edge, giving two subtrees `t₁, t₂`, reconnects them by a
new edge between the midpoints of an edge of `t₁` and an edge of `t₂` (or at the leaf, when a
subtree is a single leaf), and applies forced contractions. `d_TBR(T, T')` is the least number
of TBR operations transforming `T` into `T'` (Definition 2.6). An agreement forest (Definition
2.12) is a partition `L₁, …, L_k` of the taxa with `T|Lⱼ = T'|Lⱼ` and with the minimal subtrees
`T(Lⱼ)`, and likewise `T'(Lⱼ)`, vertex-disjoint; `m(T, T')` is the least `k - 1`. Theorem 2.13:
`d_TBR(T, T') = m(T, T')`; in particular `m` is a metric.

Agreement forests, and restrictions compared through displayed quartets, are those of
`WantedExt.Complexity.NPComplete.TBRDistanceWanted` (`IsAgreementForest`), which uses the same
theorem to phrase the NP-complete TBR DISTANCE problem but does not record the theorem itself.
Trees are the repository's `UnrootedBinaryTree`, with edge splits and quartets from
`CSLibExt.Bioinformatics.Phylogenetics.Splits`.

One TBR step is recorded through what it preserves (`IsTBRStep`). Removing an edge with sides
`A | Aᶜ` leaves the pieces `T|A` and `T|Aᶜ` (after forced contraction), and the new edge has the
same sides `A | Aᶜ` in the result. Conversely, if `A | Aᶜ` is an edge split of both `T` and `T'`
and `T|A = T'|A`, `T|Aᶜ = T'|Aᶜ`, then cutting that edge of `T` and reconnecting at the edges of
the two pieces where `T'` attaches its edge produces a tree isomorphic to `T'`. Restrictions are
compared by their quartets: `T|L = T'|L` holds iff `T` and `T'` display the same quartets on four
distinct taxa of `L` (an unrooted binary tree is determined by its quartets, Semple and Steel
2003, Corollary 6.3.8, `iso_of_displaysQuartet_iff`; with at most three taxa there is a single
tree).

Not recorded here: Theorem 3.4 (subtree and chain reductions preserve `d_TBR`) and Theorem 3.8
(fixed-parameter tractability), which need the reduction operations and a parameterized
complexity class. Bordewich and Semple (2005, Section 3) point out that one step of the original
argument for the chain reduction is incorrect as written.

Sources: B. L. Allen and M. Steel, "Subtree transfer operations and their induced metrics on
evolutionary trees", Annals of Combinatorics 5 (2001) 1–15, doi:10.1007/s00026-001-8006-8,
Definitions 1.1, 2.3, 2.6, 2.12 and Theorem 2.13; C. Semple and M. Steel, *Phylogenetics*,
Oxford University Press, 2003, Corollary 6.3.8; M. Bordewich and C. Semple, "On the
computational complexity of the rooted subtree prune and regraft distance", Annals of
Combinatorics 8 (2005) 409–423, doi:10.1007/s00026-004-0229-z.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Complexity.NPComplete.TBRDistanceWanted

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.TBRAgreementForestWanted

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open Cslib.Bioinformatics.Phylogenetics.Splits
open MetaMathlibExt.Complexity.NPComplete.TBRDistance

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The restrictions `T|L` and `T'|L` agree: `T` and `T'` display the same quartets on any four
distinct taxa of `L`. -/
def RestrictionsAgree (T T' : UnrootedBinaryTree X) (L : Finset X) : Prop :=
  ∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, ∀ d ∈ L, [a, b, c, d].Nodup →
    (DisplaysQuartet T a b c d ↔ DisplaysQuartet T' a b c d)

/-- `T'` is obtained from `T` by one **tree bisection and reconnection**: some set of taxa `A`
is a side of an edge of both trees, and the restrictions of `T` and `T'` to `A` and to its
complement agree. -/
def IsTBRStep (T T' : UnrootedBinaryTree X) : Prop :=
  ∃ A : Finset X, A ∈ edgeSplits T ∧ A ∈ edgeSplits T' ∧ RestrictionsAgree T T' A ∧
    RestrictionsAgree T T' Aᶜ

/-- `T` is transformed into a tree isomorphic to `T'` by `k` TBR operations. -/
def TBRReachIn (k : ℕ) (T T' : UnrootedBinaryTree X) : Prop :=
  ∃ f : Fin (k + 1) → UnrootedBinaryTree X, f 0 = T ∧ (f (Fin.last k)).Iso T' ∧
    ∀ i : Fin k, IsTBRStep (f i.castSucc) (f i.succ)

/-- The **TBR distance** `d_TBR(T, T')`: the least number of TBR operations transforming `T`
into `T'`. -/
noncomputable def tbrDist (T T' : UnrootedBinaryTree X) : ℕ :=
  sInf {k | TBRReachIn k T T'}

/-- The **maximum agreement forest number** `m(T, T')`: the least number of trees of an
agreement forest for `T` and `T'`, minus one. -/
noncomputable def mafNumber (T T' : UnrootedBinaryTree X) : ℕ :=
  sInf {k | ∃ F : Finpartition (Finset.univ : Finset X), IsAgreementForest T T' F ∧
    F.parts.card = k + 1}

/-- **TBR distance equals the maximum agreement forest number** (Allen and Steel 2001,
Theorem 2.13): for unrooted binary phylogenetic trees `T` and `T'` on the same taxa,
`d_TBR(T, T') = m(T, T')`.

Source: Allen and Steel (2001), Theorem 2.13. -/
public theorem_wanted tbrDist_eq_mafNumber (T T' : UnrootedBinaryTree X) :
    tbrDist T T' = mafNumber T T'

/-- **The maximum agreement forest number is a metric** on isomorphism classes (Allen and Steel
2001, Theorem 2.13, "in particular"): it vanishes exactly on isomorphic trees, is symmetric and
satisfies the triangle inequality.

Source: Allen and Steel (2001), Theorem 2.13. -/
public theorem_wanted mafNumber_isMetric (T T' T'' : UnrootedBinaryTree X) :
    (mafNumber T T' = 0 ↔ T.Iso T') ∧ mafNumber T T' = mafNumber T' T ∧
      mafNumber T T'' ≤ mafNumber T T' + mafNumber T' T''

end WantedExt.Biology.ComputationalBiology.TBRAgreementForestWanted
