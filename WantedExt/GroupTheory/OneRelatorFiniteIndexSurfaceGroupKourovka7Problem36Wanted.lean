/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# One-relator subgroups of finite index (Kourovka Notebook Problem 7.36)

Kourovka Notebook, Archive of Solved Problems, Problem 7.36 (O. V. Mel'nikov): is it true that every
residually finite group in which every subgroup of finite index (including the group itself) is
defined by a single defining relation is either free or isomorphic to the fundamental group of a
compact surface?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.OnCoherenceOfOneRelatorGroupsWanted

@[expose] public section

namespace MathlibExt.GroupTheory.OneRelatorFiniteIndexSurfaceGroupKourovka7Problem36Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 7.36 (O. V.
Mel'nikov). UnsolvedMath record UM-00700433 (`KOU-7.36`), dataset ulamai/UnsolvedMath v1.8.0.

Defined by a single defining relation is `Group.OneRelator` from
`WantedExt/GroupTheory/OnCoherenceOfOneRelatorGroupsWanted.lean`: isomorphic to `⟨x₁, …, xₙ | r⟩`
for some `n` and word `r` (`r = 1` allowed, so free groups of finite rank qualify). Fundamental
groups of compact surfaces are given by the classification of surfaces: free groups (surfaces with
boundary) and the closed surface groups `⟨a₁, b₁, …, a_g, b_g | [a₁, b₁] ⋯ [a_g, b_g]⟩` and `⟨c₁, …,
c_k | c₁² ⋯ c_k²⟩`, `k ≥ 1`. The group is assumed infinite: a finite cyclic group `ℤ/n`, `n ≥ 3`,
meets the hypotheses literally and is neither free nor a surface group, so the question concerns
infinite groups (the Archive's counterexamples are infinite).
-/

open MathlibExt.GroupTheory.OnCoherenceOfOneRelatorGroupsWanted

/-- The fundamental group of the closed orientable surface of genus `g`:
`⟨a₁, b₁, …, a_g, b_g | [a₁, b₁] ⋯ [a_g, b_g]⟩`, with `aᵢ = (i, false)` and `bᵢ = (i, true)`. -/
abbrev orientableSurfaceGroup (g : ℕ) : Type :=
  PresentedGroup ({((List.finRange g).map fun i =>
    FreeGroup.of (i, false) * FreeGroup.of (i, true) * (FreeGroup.of (i, false))⁻¹ *
      (FreeGroup.of (i, true))⁻¹).prod} : Set (FreeGroup (Fin g × Bool)))

/-- The fundamental group of the closed non-orientable surface of genus `k`:
`⟨c₁, …, c_k | c₁² ⋯ c_k²⟩`. -/
abbrev nonorientableSurfaceGroup (k : ℕ) : Type :=
  PresentedGroup ({((List.finRange k).map fun i => FreeGroup.of i ^ 2).prod} :
    Set (FreeGroup (Fin k)))

/-- Kourovka 7.36 (O. V. Mel'nikov): an infinite residually finite group all of whose subgroups
of finite index (the group itself included) are defined by a single defining relation is free or
isomorphic to the fundamental group of a compact surface (a free group when the surface has
boundary, one of the closed surface groups above otherwise). -/
def oneRelatorFiniteIndexFreeOrSurface : Prop :=
  ∀ (G : Type) [Group G], Infinite G → Group.ResiduallyFinite G →
    (∀ H : Subgroup G, H.FiniteIndex → Group.OneRelator H) →
    (∃ ι : Type, Nonempty (G ≃* FreeGroup ι)) ∨
      (∃ g : ℕ, Nonempty (G ≃* orientableSurfaceGroup g)) ∨
      ∃ k : ℕ, 1 ≤ k ∧ Nonempty (G ≃* nonorientableSurfaceGroup k)

/--
Resolved false: the Kourovka Archive answers 7.36 "No", with the counterexamples `Hₙ = ⟨x, y | y⁻¹xy
= xⁿ⟩`, `n = 2, 3, …`, every subgroup of finite index of which is isomorphic to some `H_m` (Churkin
1982; also stated in the introduction of arXiv:2110.14834: every finite index subgroup of `BS(1, n)`
is again some `BS(1, k)`). Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in
Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved
Problems, Problem 7.36 (O. V. Mel'nikov); resolution: V. A. Churkin, Abstracts of the 8th All-Union
Symposium on Group Theory, Kiev, 1982, 139-140 (Russian), Kourovka Archive, Problem 7.36: No; for
H_n = ⟨x, y | y⁻¹xy = xⁿ⟩, n ≥ 2, every subgroup of finite index is isomorphic to some H_m,
https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted oneRelatorFiniteIndexFreeOrSurface_refuted :
    ¬ oneRelatorFiniteIndexFreeOrSurface

end MathlibExt.GroupTheory.OneRelatorFiniteIndexSurfaceGroupKourovka7Problem36Wanted
