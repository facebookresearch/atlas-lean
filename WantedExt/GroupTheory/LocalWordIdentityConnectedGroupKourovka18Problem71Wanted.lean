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

/-- Kourovka 18.71 (N. Aronszajn; J. Mycielski): if a word `W(x, y)` (an element of the free group
on `x`, `y`) takes the value `1` on a nonempty open subset of `G × G`, where `G` is a connected
Hausdorff topological group, then `W(x, y) = 1` for all `x, y ∈ G`. -/
def localWordIdentityHoldsGlobally : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G],
    ConnectedSpace G → ∀ (W : FreeGroup (Fin 2)) (U : Set (G × G)), IsOpen U → U.Nonempty →
      (∀ p ∈ U, FreeGroup.lift ![p.1, p.2] W = 1) → ∀ x y : G, FreeGroup.lift ![x, y] W = 1

/--
Resolved false: the Kourovka Notebook (21st issue) answers 18.71 "No, not necessarily"
(Reznichenko-Zyabrev, 2024): for odd `n` there is a connected Hausdorff topological group in which
`xⁿ = 1` holds on a neighbourhood `U` of the identity but not everywhere, so the word `W(x, y) = xⁿ`
is `1` on the nonempty open set `U × G`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
18.71 (J. Mycielski); resolution: I. N. Zyabrev and E. A. Reznichenko, On identities in connected
topological groups, preprint, arXiv:2406.05203 (2024), abstract: a connected (indeed path-connected)
Hausdorff topological group in which, for an odd n, the identity x^n = e holds in some neighbourhood
of the identity but not in the whole group; the Kourovka Notebook (21st issue) marks 18.71 solved
(odd n > 10^10), https://arxiv.org/abs/2406.05203.
-/
public theorem_wanted localWordIdentityHoldsGlobally_refuted : ¬ localWordIdentityHoldsGlobally

end MathlibExt.GroupTheory.LocalWordIdentityConnectedGroupKourovka18Problem71Wanted
