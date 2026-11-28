/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Groups isomorphic to every extension of themselves by themselves (Kourovka Notebook Problem 12.44)

Kourovka Notebook, Archive of Solved Problems, Problem 12.44 (P. Hall; J. C. Lennox): is there a
non-trivial group which is isomorphic with every proper extension of itself by itself?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

namespace MathlibExt.GroupTheory.HallGroupSelfExtensionKourovka12Problem44Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.44 (P. Hall;
J. C. Lennox). UnsolvedMath record UM-00700863 (`KOU-12.44`), dataset ulamai/UnsolvedMath v1.8.0.

Extensions follow Göbel and Shelah's Definition 1.1 of a Hall group: every group `H` with a normal
subgroup `N ≅ G` and `H ⧸ N ≅ G` is isomorphic to `G`. "Proper" adds nothing for nontrivial `G`
(then `N ≠ H` automatically). Groups are in `Type`, which contains a copy of every extension of a
group in `Type` by itself.
-/

/-- **Hall group.** A group $G$ is a Hall group (in the sense of Göbel and Shelah) when it is
isomorphic to every extension of itself by itself: for every group $H$ and every normal subgroup
$N$ of $H$ with $N \cong G$ and $H/N \cong G$, also $H \cong G$. -/
def IsHallGroup (G : Type) [Group G] : Prop :=
  ∀ (H : Type) [Group H] (N : Subgroup H) [N.Normal],
    Nonempty (N ≃* G) → Nonempty ((H ⧸ N) ≃* G) → Nonempty (H ≃* G)

/-- **Hall's problem on self-extensions (Kourovka Problem 12.44).** There is a nontrivial group $G$
that is a Hall group, that is, isomorphic to every extension of itself by itself: every group $H$
with a normal subgroup $N \cong G$ such that $H/N \cong G$ is isomorphic to $G$. -/
def existsGroupIsoToSelfExtensions : Prop :=
  ∃ (G : Type) (_ : Group G), Nontrivial G ∧ IsHallGroup G

/--
**Existence of Hall groups (Göbel–Shelah; Kourovka Problem 12.44).** There is a nontrivial group
$G$ that is isomorphic to every extension of itself by itself: every group $H$ with a normal
subgroup $N \cong G$ such that $H/N \cong G$ is isomorphic to $G$.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.44
(P. Hall; J. C. Lennox); resolution: R. Göbel and S. Shelah, Philip Hall's problem on non-Abelian
splitters, Math. Proc. Cambridge Philos. Soc. 134 (2003), no. 1, 23-31, arXiv:math/0009091,
Definition 1.1 and Corollary 1.5 (L^ω is a Hall group for every rigid group L), with the existence
of rigid groups (Theorem 3.1); Kourovka Archive, Problem 12.44, https://arxiv.org/abs/math/0009091.
-/
public theorem_wanted existsGroupIsoToSelfExtensions_holds : existsGroupIsoToSelfExtensions

end MathlibExt.GroupTheory.HallGroupSelfExtensionKourovka12Problem44Wanted
