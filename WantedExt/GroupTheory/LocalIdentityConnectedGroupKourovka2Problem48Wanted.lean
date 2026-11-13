/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local identities in connected topological groups (Kourovka Notebook Problem 2.48)

Kourovka Notebook, Problem 2.48 (V. P. Platonov; question of N. Aronszajn), marked solved in the
21st issue: let `G` be a connected topological group locally satisfying some identical relation
`f|_U = 1`, where `U` is a neighborhood of the identity element of `G`. Is it then true that `f|_G =
1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

namespace MathlibExt.GroupTheory.LocalIdentityConnectedGroupKourovka2Problem48Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 2.48 (V. P. Platonov; question of N.
Aronszajn). UnsolvedMath record UM-00700121 (`KOU-2.48`), dataset ulamai/UnsolvedMath v1.8.0.

A word `f` in `k` variables is an element of `FreeGroup (Fin k)`; `f|_U = 1` means `f(u₁, …, u_k) =
1` for all `uᵢ ∈ U`. Topological groups are Hausdorff, which weakens the refuted claim; the
Reznichenko-Zyabrev group is a path-connected Hausdorff group. Kourovka 18.71 (a word in two
variables equal to `1` on an arbitrary open subset of `G × G`) is a different problem, resolved by
the same preprint, and is the separate entry
`LocalWordIdentityConnectedGroupKourovka18Problem71Wanted`.
-/

/-- Kourovka 2.48 (N. Aronszajn; V. P. Platonov): if a word `f` in `k` variables is an identity
on some neighbourhood `U` of `1` in a connected (Hausdorff) topological group `G`, that is,
`f(u₁, …, u_k) = 1` for all `u₁, …, u_k ∈ U`, then `f` is an identity of `G`. -/
def localIdentityIsGlobal : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [ConnectedSpace G] (k : ℕ) (f : FreeGroup (Fin k)),
    (∃ U ∈ nhds (1 : G), ∀ u : Fin k → G, (∀ i, u i ∈ U) → FreeGroup.lift u f = 1) →
      ∀ g : Fin k → G, FreeGroup.lift g f = 1

/--
Resolved false: Zyabrev and Reznichenko (2024) construct a path-connected Hausdorff topological
group in which, for an odd `n` (`n ≥ 665` in the preprint; the Kourovka Notebook's note says `n ≥
10¹⁰`), the identity `xⁿ = 1` holds on a neighbourhood of the identity but not in the whole group;
the Kourovka Notebook (21st issue) marks 2.48 solved, "No, not necessarily". Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 2.48 (V. P. Platonov; question of N. Aronszajn); resolution: I.
N. Zyabrev and E. A. Reznichenko, On identities in connected topological groups, preprint,
arXiv:2406.05203 (2024), Abstract: a path-connected Hausdorff topological group in which, for an odd
n ≥ 665, the identity x^n = e holds in a neighbourhood of the identity but not in the whole group;
the Kourovka Notebook (21st issue) marks 2.48 solved, for odd n ≥ 10^10,
https://arxiv.org/abs/2406.05203.
-/
public theorem_wanted localIdentityIsGlobal_refuted : ¬ localIdentityIsGlobal

end MathlibExt.GroupTheory.LocalIdentityConnectedGroupKourovka2Problem48Wanted
