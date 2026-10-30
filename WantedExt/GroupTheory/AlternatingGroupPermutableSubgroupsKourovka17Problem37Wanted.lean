/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Permutable subgroups of large alternating groups (Kourovka Notebook Problem 17.37)

Kourovka Notebook, Problem 17.37 (A. F. Vasil'ev, A. N. Skiba): is there an integer `n` such that
for all `m > n` the alternating group `A_m` has no non-trivial `A_m`-permutable subgroups? (A
subgroup `A` of `G` is `G`-permutable if for every subgroup `B` of `G` there is `x ∈ G` with `AB^x =
B^xA`; Problem 17.112.)
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.SpecificGroups.Alternating

@[expose] public section

namespace MathlibExt.GroupTheory.AlternatingGroupPermutableSubgroupsKourovka17Problem37Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 17.37 (A. F. Vasil'ev, A. N. Skiba).
UnsolvedMath record UM-00701339 (`KOU-17.37`), dataset ulamai/UnsolvedMath v1.8.0.

`1` and `A_m` itself are always `A_m`-permutable, so "non-trivial" means different from both, as in
the Notebook's comments to 17.112 ("a proper `G`-permutable subgroup") and in the statement of the
Yang-Galt theorem by Zhang (arXiv:2610.12329, Introduction: no `A_n`, `n ≥ N`, has a proper
nontrivial `A_n`-permutable subgroup). `A_m` is `alternatingGroup (Fin m)`, products of subgroups
are pointwise set products, and `B^x` is the image of `B` under conjugation by `x` (the direction of
conjugation is immaterial as `x` ranges over `G`).
-/

open scoped Pointwise

/-- A subgroup `A` of `G` is `G`-permutable (Kourovka 17.112): for every subgroup `B` of `G` some
conjugate `B^x` of `B` permutes with `A`, that is, `A B^x = B^x A`. -/
def IsGPermutable {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  ∀ B : Subgroup G, ∃ x : G,
    (A : Set G) * (B.map (MulAut.conj x).toMonoidHom : Set G) =
      (B.map (MulAut.conj x).toMonoidHom : Set G) * (A : Set G)

/-- Kourovka 17.37 (A. F. Vasil'ev, A. N. Skiba): there is `n` such that for every `m > n` the
alternating group `A_m` has no `A_m`-permutable subgroups other than `1` and `A_m` (which are
always `A_m`-permutable). -/
def alternatingGroupNoProperPermutableSubgroups : Prop :=
  ∃ n : ℕ, ∀ m : ℕ, n < m → ∀ A : Subgroup (alternatingGroup (Fin m)),
    IsGPermutable A → A = ⊥ ∨ A = ⊤

/--
Resolved true: Yang and Galt prove that there is `N` such that for every `n ≥ N` the alternating
group `A_n` has no `A_n`-permutable subgroups other than `1` and `A_n` (as stated by Zhang); the
Kourovka Notebook (21st issue) answers 17.37 "Yes, there is". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Problem 17.37 (A. F. Vasil'ev, A. N. Skiba); resolution: N. Yang and A.
Galt, Bull. Malays. Math. Sci. Soc. (2) 46 (2023), no. 5, Paper no. 177, as stated in S. Zhang,
Ordinary G-permutable subgroups of finite simple groups, preprint, arXiv:2610.12329 (2026), Zhang,
Introduction (Yang and Galt proved that there is N ≥ 7 such that no A_n with n ≥ N has a proper
nontrivial A_n-permutable subgroup, with A_n-permutable as in Problem 17.112); the Kourovka Notebook
(21st issue) marks 17.37 solved (Yes, there is), https://arxiv.org/abs/2610.12329.
-/
public theorem_wanted alternatingGroupNoProperPermutableSubgroups_holds :
    alternatingGroupNoProperPermutableSubgroups

end MathlibExt.GroupTheory.AlternatingGroupPermutableSubgroupsKourovka17Problem37Wanted
