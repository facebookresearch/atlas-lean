/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local identities in connected topological groups (Kourovka Notebook Problem 18.71)

Kourovka Notebook, Problem 18.71 (N. Aronszajn; J. Mycielski), marked solved in the 21st issue:
suppose that `W(x, y) = 1` in an open subset of `G × G`, where `G` is a connected topological group.
Must `W(x, y) = 1` for all `(x, y) ∈ G × G`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.LocalWordIdentityConnectedGroupKourovka18Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 18.71 (J. Mycielski). UnsolvedMath record
UM-00701500 (`KOU-18.71`), dataset ulamai/UnsolvedMath v1.8.0.

`W` is an element of the free group on `x, y`, evaluated by `FreeGroup.lift`; the open subset is
nonempty (an empty one makes the hypothesis vacuous). Topological groups are taken Hausdorff: this
only weakens the claim, so its refutation is the stronger statement, and the resolving group is
Hausdorff.
-/

/-- **Local word identities in connected groups (Kourovka 18.71).** The statement that for every
connected Hausdorff topological group $G$ and every word $W(x, y)$ in the free group on two
generators $x$, $y$, if $W(a, b) = 1$ for all $(a, b)$ in some nonempty open subset of $G \times G$,
then $W(a, b) = 1$ for all $a, b \in G$.

The problem is posed for connected topological groups; here they are also taken to be Hausdorff,
which weakens the statement. -/
def localWordIdentityHoldsGlobally : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G],
    ConnectedSpace G → ∀ (W : FreeGroup (Fin 2)) (U : Set (G × G)), IsOpen U → U.Nonempty →
      (∀ p ∈ U, FreeGroup.lift ![p.1, p.2] W = 1) → ∀ x y : G, FreeGroup.lift ![x, y] W = 1

/--
**Local word identities need not hold globally in connected groups.** There are a connected
Hausdorff topological group $G$, a word $W(x, y)$ in the free group on two generators $x$, $y$ and
a nonempty open subset $U$ of $G \times G$ such that $W(a, b) = 1$ for all $(a, b) \in U$ but
$W(a, b) \ne 1$ for some $a, b \in G$. This answers Kourovka Notebook Problem 18.71 in the
negative.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
18.71 (J. Mycielski); resolution: I. N. Zyabrev and E. A. Reznichenko, On identities in connected
topological groups, preprint, arXiv:2406.05203 (2024), abstract: a connected (indeed path-connected)
Hausdorff topological group in which, for an odd n, the identity x^n = e holds in some neighbourhood
of the identity but not in the whole group; the Kourovka Notebook (21st issue) marks 18.71 solved
(odd n > 10^10), https://arxiv.org/abs/2406.05203.
-/
public theorem_wanted localWordIdentityHoldsGlobally_refuted : ¬ localWordIdentityHoldsGlobally

end MathlibExt.GroupTheory.LocalWordIdentityConnectedGroupKourovka18Problem71Wanted
