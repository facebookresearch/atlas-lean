/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Proper abelian subgroups in normal subgroups of prime index (Kourovka Notebook Problem 2.29)

Kourovka Notebook, Archive of Solved Problems, Problem 2.29 (P. G. Kontorovich, V. T. Nagrebetskiĭ):
does the class of finite groups in which every proper abelian subgroup is contained in a proper
normal subgroup coincide with the class of finite groups in which every proper abelian subgroup is
contained in a proper normal subgroup of prime index?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianSubgroupPrimeIndexNormalKourovka2Problem29Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 2.29 (P. G.
Kontorovich, V. T. Nagrebetskiĭ). UnsolvedMath record UM-00700104 (`KOU-2.29`), dataset
ulamai/UnsolvedMath v1.8.0.

"The classes coincide" is stated as an equivalence for every finite group in `Type`; the second
class is contained in the first, so the content is a group in the first class but not in the second.
Prime index is `N.index.Prime`.
-/

/-- Kourovka 2.29 (P. G. Kontorovich, V. T. Nagrebetskiĭ): a finite group in which every proper
abelian subgroup lies in a proper normal subgroup is the same as a finite group in which every
proper abelian subgroup lies in a normal subgroup of prime index. -/
def abelianInProperNormalIffPrimeIndex : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    (∀ A : Subgroup G, A ≠ ⊤ → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊤ ∧ A ≤ N) ↔
    (∀ A : Subgroup G, A ≠ ⊤ → (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) →
      ∃ N : Subgroup G, N.Normal ∧ N.index.Prime ∧ A ≤ N)

/--
Resolved false: the Kourovka Archive answers 2.29 "No" with the Bergman-Isaacs example `A ≀ B`, `B`
finite perfect of rank `r` and `A = ⊕_{p ∣ |B|} (ℤ/pℤ)^{r+1}`: every proper abelian subgroup lies in
a proper normal subgroup, but the base group lies in no proper normal subgroup of prime index, since
the quotient by it is `B = [B, B]`. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 2.29 (P. G. Kontorovich, V. T. Nagrebetskiĭ); resolution: G. M. Bergman and
I. M. Isaacs, letter of 17 June 1974, Kourovka Archive, Problem 2.29: No; for a finite perfect group
B ≠ 1 of rank r and A = ⊕_{p ∣ |B|} (ℤ/pℤ)^{r+1}, the wreath product A ≀ B has every proper abelian
subgroup in a proper normal subgroup, while its base group is in no proper normal subgroup of prime
index, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted abelianInProperNormalIffPrimeIndex_refuted :
    ¬ abelianInProperNormalIffPrimeIndex

end MathlibExt.GroupTheory.AbelianSubgroupPrimeIndexNormalKourovka2Problem29Wanted
