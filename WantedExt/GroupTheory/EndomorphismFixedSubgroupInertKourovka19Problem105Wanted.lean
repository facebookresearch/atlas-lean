/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fixed subgroups of endomorphisms of free groups are inert (Kourovka Notebook Problem 19.105)

Kourovka Notebook, Problem 19.105 (E. Ventura), marked solved in the 21st issue: is it true that the
fixed subgroups of endomorphisms of `F` are inert?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.EndomorphismFixedSubgroupInertKourovka19Problem105Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 19.105 (E. Ventura). UnsolvedMath record
UM-00701653 (`KOU-19.105`), dataset ulamai/UnsolvedMath v1.8.0.

`F` is a free group of finite rank, `FreeGroup (Fin n)`; the rank `r(H) ∈ ℕ∞` is the least size of a
finite generating set (`⊤` when `H` is not finitely generated). In `Fₙ` every compressed or inert
subgroup has rank at most `n`, so Jaikin-Zapirain's theorem on finitely generated subgroups covers
all of them. Mathlib's `Group.rank` needs a `Group.FG` instance, so the rank is defined here for
every subgroup, with `⊤` for the non-finitely generated ones. The fixed subgroup of `φ` is
`MonoidHom.eqLocus φ id`.
-/

/-- The rank `r(H) ∈ ℕ∞`: the least size of a finite generating set of `H` (`⊤` if `H` is not
finitely generated). -/
noncomputable def subgroupRank {G : Type} [Group G] (H : Subgroup G) : ℕ∞ :=
  ⨅ (s : Finset G) (_ : Subgroup.closure (s : Set G) = H), (s.card : ℕ∞)

/-- `H ≤ F` is inert: `r(H ∩ K) ≤ r(K)` for every subgroup `K`. -/
def IsInert {n : ℕ} (H : Subgroup (FreeGroup (Fin n))) : Prop :=
  ∀ K : Subgroup (FreeGroup (Fin n)), subgroupRank (H ⊓ K) ≤ subgroupRank K

/-- Kourovka 19.105 (E. Ventura), for free groups of finite rank: the fixed subgroup
`{x | φ x = x}` of every endomorphism `φ` of `Fₙ` is inert. -/
def endomorphismFixedSubgroupInert : Prop :=
  ∀ (n : ℕ) (φ : FreeGroup (Fin n) →* FreeGroup (Fin n)),
    IsInert (MonoidHom.eqLocus φ (MonoidHom.id _))

/--
Resolved true: the Kourovka Notebook (21st issue) answers 19.105 "Yes, it is true", citing A.
Jaikin-Zapirain (2024), whose Corollary 1.2 proves that compressed and inert are equivalent for
finitely generated subgroups of a free group. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Problem 19.105 (E. Ventura); resolution: A. Jaikin-Zapirain, Free groups are L^2-subgroup rigid,
preprint, arXiv:2403.09515 (2024), Corollary 1.2: for a finitely generated subgroup of a free group,
compressed iff inert; the Kourovka Notebook (21st issue) answers 19.105 "Yes, it is true" citing
this preprint, https://arxiv.org/abs/2403.09515.
-/
public theorem_wanted endomorphismFixedSubgroupInert_holds : endomorphismFixedSubgroupInert

end MathlibExt.GroupTheory.EndomorphismFixedSubgroupInertKourovka19Problem105Wanted
