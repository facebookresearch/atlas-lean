/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Intersections of compressed subgroups (Kourovka Notebook Problem 19.103)

Kourovka Notebook, Problem 19.103 (E. Ventura), marked solved in the 21st issue: is it true that an
intersection of compressed subgroups is compressed? (It is known that arbitrary intersections of
inert subgroups are inert.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.CompressedSubgroupIntersectionKourovka19Problem103Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.103 (E. Ventura). UnsolvedMath record
UM-00701651 (`KOU-19.103`), dataset ulamai/UnsolvedMath v1.8.0.

`F` is a free group of finite rank, `FreeGroup (Fin n)`; the rank `r(H) ∈ ℕ∞` is the least size of a
finite generating set (`⊤` when `H` is not finitely generated). In `Fₙ` every compressed or inert
subgroup has rank at most `n`, so Jaikin-Zapirain's theorem on finitely generated subgroups covers
all of them. Mathlib's `Group.rank` needs a `Group.FG` instance, so the rank is defined here for
every subgroup, with `⊤` for the non-finitely generated ones. The target is the intersection of two
compressed subgroups, the statement of Jaikin-Zapirain's Corollary 1.3(1), which he gives as the
answer to 19.103; intersections of arbitrary families are not covered.
-/

/-- The rank `r(H) ∈ ℕ∞`: the least size of a finite generating set of `H` (`⊤` if `H` is not
finitely generated). -/
noncomputable def subgroupRank {G : Type} [Group G] (H : Subgroup G) : ℕ∞ :=
  ⨅ (s : Finset G) (_ : Subgroup.closure (s : Set G) = H), (s.card : ℕ∞)

/-- `H ≤ F` is compressed: `r(H) ≤ r(K)` for every subgroup `K ⊇ H`. -/
def IsCompressed {n : ℕ} (H : Subgroup (FreeGroup (Fin n))) : Prop :=
  ∀ K : Subgroup (FreeGroup (Fin n)), H ≤ K → subgroupRank H ≤ subgroupRank K

/-- Kourovka 19.103 (E. Ventura), for free groups of finite rank: the intersection of two
compressed subgroups of `Fₙ` is compressed. -/
def intersectionOfCompressedCompressed : Prop :=
  ∀ (n : ℕ) (H K : Subgroup (FreeGroup (Fin n))), IsCompressed H → IsCompressed K →
    IsCompressed (H ⊓ K)

/--
Resolved true: the Kourovka Notebook (21st issue) answers 19.103 "Yes, it is true" (A.
Jaikin-Zapirain, 2024), whose Corollary 1.3(1) states that the intersection of two compressed
subgroups of a free group is compressed. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem
19.103 (E. Ventura); resolution: A. Jaikin-Zapirain, Free groups are L^2-subgroup rigid, preprint,
arXiv:2403.09515 (2024), Corollary 1.3(1) (citing Kourovka 19.103): the intersection of two
compressed subgroups of a free group is again compressed, from Corollary 1.2 (compressed iff inert
for finitely generated subgroups); the Kourovka Notebook (21st issue) marks 19.103 solved,
https://arxiv.org/abs/2403.09515.
-/
public theorem_wanted intersectionOfCompressedCompressed_holds : intersectionOfCompressedCompressed

end MathlibExt.GroupTheory.CompressedSubgroupIntersectionKourovka19Problem103Wanted
