/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Compressed subgroups of free groups are inert (Kourovka Notebook Problem 19.102)

Kourovka Notebook, Problem 19.102 (E. Ventura), marked solved in the 21st issue: a subgroup `H` of a
free group `F` is inert if `r(H ∩ K) ≤ r(K)` for every `K ≤ F`, and compressed if `r(H) ≤ r(K)` for
every `H ≤ K ≤ F`. Is it true that compressed subgroups are inert?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.CompressedSubgroupInertKourovka19Problem102Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.102 (E. Ventura). UnsolvedMath record
UM-00701650 (`KOU-19.102`), dataset ulamai/UnsolvedMath v1.8.0.

`F` is a free group of finite rank, `FreeGroup (Fin n)`; the rank `r(H) ∈ ℕ∞` is the least size of a
finite generating set (`⊤` when `H` is not finitely generated). In `Fₙ` every compressed or inert
subgroup has rank at most `n`, so Jaikin-Zapirain's theorem on finitely generated subgroups covers
all of them. Mathlib's `Group.rank` needs a `Group.FG` instance, so the rank is defined here for
every subgroup, with `⊤` for the non-finitely generated ones. Free groups of infinite rank are not
covered.
-/

/-- **Rank of a subgroup.** For a subgroup $H$ of a group $G$, the rank
$r(H) \in \mathbb{N} \cup \{\infty\}$ is the least size of a finite subset of $G$ that generates
$H$, with $r(H) = \infty$ when $H$ is not finitely generated. -/
noncomputable def subgroupRank {G : Type} [Group G] (H : Subgroup G) : ℕ∞ :=
  ⨅ (s : Finset G) (_ : Subgroup.closure (s : Set G) = H), (s.card : ℕ∞)

/-- **Inert subgroup of a free group of finite rank.** Let $F_n$ be the free group on $n$
generators and $r(K) \in \mathbb{N} \cup \{\infty\}$ the rank of a subgroup $K$. A subgroup $H$ of
$F_n$ is inert when $r(H \cap K) \le r(K)$ for every subgroup $K$ of $F_n$. -/
def IsInert {n : ℕ} (H : Subgroup (FreeGroup (Fin n))) : Prop :=
  ∀ K : Subgroup (FreeGroup (Fin n)), subgroupRank (H ⊓ K) ≤ subgroupRank K

/-- **Compressed subgroup of a free group of finite rank.** Let $F_n$ be the free group on $n$
generators and $r(K) \in \mathbb{N} \cup \{\infty\}$ the rank of a subgroup $K$. A subgroup $H$ of
$F_n$ is compressed when $r(H) \le r(K)$ for every subgroup $K$ of $F_n$ containing $H$. -/
def IsCompressed {n : ℕ} (H : Subgroup (FreeGroup (Fin n))) : Prop :=
  ∀ K : Subgroup (FreeGroup (Fin n)), H ≤ K → subgroupRank H ≤ subgroupRank K

/-- **Ventura's compressed-implies-inert problem in finite rank (Kourovka 19.102).** The
proposition that for every $n \in \mathbb{N}$, every compressed subgroup of the free group $F_n$ on
$n$ generators is inert. -/
def compressedSubgroupsInert : Prop :=
  ∀ (n : ℕ) (H : Subgroup (FreeGroup (Fin n))), IsCompressed H → IsInert H

/--
**Compressed subgroups of free groups of finite rank are inert (Kourovka 19.102).** For every
$n \in \mathbb{N}$, every compressed subgroup $H$ of the free group $F_n$ on $n$ generators is
inert.

The Kourovka Notebook (21st issue) answers 19.102 "Yes, it is true" (A. Jaikin-Zapirain, 2024),
whose Corollary 1.2 proves that compressed and inert are equivalent for finitely generated
subgroups of a free group.

Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 19.102 (E. Ventura); resolution: A. Jaikin-Zapirain, Free groups are L^2-subgroup rigid,
preprint, arXiv:2403.09515 (2024), abstract and Corollary 1.2: for a finitely generated subgroup H
of a free group F, H is compressed iff H is inert iff H is L²-independent, answering the question of
Dicks and Ventura (Kourovka 19.102); the Kourovka Notebook (21st issue) marks 19.102 solved,
https://arxiv.org/abs/2403.09515.
-/
public theorem_wanted compressedSubgroupsInert_holds : compressedSubgroupsInert

end MathlibExt.GroupTheory.CompressedSubgroupInertKourovka19Problem102Wanted
