/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Periodic products of two locally finite groups (Kourovka Notebook Problem 2.83)

Kourovka Notebook, Archive of Solved Problems, Problem 2.83 (V. P. Shunkov): suppose that a periodic
group `G` is the product of two locally finite subgroups. Is then `G` locally finite?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Torsion

@[expose] public section

namespace MathlibExt.GroupTheory.ProductLocallyFiniteSubgroupsKourovka2Problem83Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.83 (V. P.
Shunkov). UnsolvedMath record UM-00700153 (`KOU-2.83`), dataset ulamai/UnsolvedMath v1.8.0.

`G = AB` means every element is a product `a b` with `a ∈ A`, `b ∈ B`; locally finite means every
finitely generated subgroup is finite; periodic is `IsMulTorsion G`.
-/

/-- A subgroup is locally finite: each of its finitely generated subgroups is finite. -/
def IsLocallyFiniteSubgroup {G : Type} [Group G] (A : Subgroup G) : Prop :=
  ∀ s : Finset G, (s : Set G) ⊆ A → (Subgroup.closure (s : Set G) : Set G).Finite

/-- Kourovka 2.83 (V. P. Shunkov): a periodic group `G = AB` that is the product of two locally
finite subgroups `A` and `B` is locally finite. -/
def periodicProductLocallyFiniteIsLocallyFinite : Prop :=
  ∀ (G : Type) [Group G], IsMulTorsion G → ∀ A B : Subgroup G,
    IsLocallyFiniteSubgroup A → IsLocallyFiniteSubgroup B →
    (∀ g : G, ∃ a ∈ A, ∃ b ∈ B, g = a * b) → IsLocallyFiniteSubgroup (⊤ : Subgroup G)

/--
Resolved false: the Kourovka Archive answers 2.83 "Not always", citing Sushchanskii (1990). Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.83 (V. P. Shunkov);
resolution: V. I. Sushchanskii, Math. USSR-Sb. 67 (1990), no. 2, 535-553, Kourovka Archive, Problem
2.83: Not always (Sushchanskii), https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted periodicProductLocallyFiniteIsLocallyFinite_refuted :
    ¬ periodicProductLocallyFiniteIsLocallyFinite

end MathlibExt.GroupTheory.ProductLocallyFiniteSubgroupsKourovka2Problem83Wanted
