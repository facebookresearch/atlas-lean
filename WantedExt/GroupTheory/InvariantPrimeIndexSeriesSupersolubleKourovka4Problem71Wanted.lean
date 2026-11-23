/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Automorphism groups with an invariant series of prime indices (Kourovka Notebook Problem 4.71)

Kourovka Notebook, Archive of Solved Problems, Problem 4.71 (L. A. Shemetkov): let A be a group of
automorphisms of a finite group G which has a series of A-invariant subgroups G = G_0 > ⋯ > G_k = 1
such that every |G_i : G_(i+1)| is prime; prove that A is supersoluble.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import WantedExt.GroupTheory.AbnormalSupersolubleFactorizationKourovka19Problem100Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.InvariantPrimeIndexSeriesSupersolubleKourovka4Problem71Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.71 (L. A.
Shemetkov). UnsolvedMath record UM-00700278 (`KOU-4.71`), dataset ulamai/UnsolvedMath v1.8.0.

The subgroups `G_i` of the series need not be normal; each is invariant under every element of `A`,
a subgroup of `MulAut G`, and `|G_i : G_(i+1)|` is `relIndex`. Supersoluble means having a series of
normal subgroups with cyclic factors: `IsSupersoluble` of the Kourovka 19.100 entry, reused here.
-/

open MathlibExt.GroupTheory.AbnormalSupersolubleFactorizationKourovka19Problem100Wanted
  (IsSupersoluble)

/-- Kourovka 4.71 (L. A. Shemetkov): if a group `A` of automorphisms of a finite group `G` leaves
invariant every term of a series `G = G₀ ≥ G₁ ≥ ⋯ ≥ G_k = 1` of subgroups of `G` (not necessarily
normal) in which every index `|G_i : G_(i+1)|` is prime, then `A` is supersoluble. -/
def invariantPrimeIndexSeriesSupersoluble : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup (MulAut G)) (k : ℕ) (s : ℕ → Subgroup G),
    s 0 = ⊤ → s k = ⊥ → (∀ i < k, s (i + 1) ≤ s i ∧ ((s (i + 1)).relIndex (s i)).Prime) →
    (∀ i ≤ k, ∀ a ∈ A, ∀ g ∈ s i, a g ∈ s i) → IsSupersoluble A

/--
Resolved true: the Kourovka Archive records 4.71 as proved by Shemetkov (Math. USSR-Sb. 23 (1974),
593-611): a group of automorphisms of a finite group leaving invariant every term of a series of
subgroups with prime indices is supersoluble. Source: E. I. Khukhro and V. D. Mazurov (eds.),
Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026),
Archive of Solved Problems, Problem 4.71 (L. A. Shemetkov); resolution: L. A. Shemetkov, Graduated
formations of groups, Math. USSR-Sb. 23 (1974), 593-611, Kourovka Archive, Problem 4.71: This was
proved (Shemetkov), https://doi.org/10.1070/SM1974v023n04ABEH002184.
-/
public theorem_wanted invariantPrimeIndexSeriesSupersoluble_holds :
    invariantPrimeIndexSeriesSupersoluble

end MathlibExt.GroupTheory.InvariantPrimeIndexSeriesSupersolubleKourovka4Problem71Wanted
