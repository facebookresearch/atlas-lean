/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Independent bases of quasi-identities of non-abelian free groups (Kourovka Notebook Problem 5.51)

Kourovka Notebook, Archive of Solved Problems, Problem 5.51 (D. M. Smirnov): does a non-abelian free
group have an independent basis for its quasi-laws?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.GroupLawsShared

@[expose] public section

namespace MathlibExt.GroupTheory.QuasiIdentityBasisFreeGroupKourovka5Problem51Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.51 (D. M.
Smirnov). UnsolvedMath record UM-00700332 (`KOU-5.51`), dataset ulamai/UnsolvedMath v1.8.0.

A non-abelian free group is `FreeGroup α` with at least two generators. Quasi-laws are the
quasi-identities holding in the group (`QuasiIdentity` of the Kourovka 14.25 entry, reused here);
consequence and independent bases are those of the shared module
`WantedExt.GroupTheory.GroupLawsShared`. All non-abelian free groups have the same quasi-laws: a
quasi-identity involves finitely many variables, and free groups of finite rank at least two embed
in one another.
-/

open MathlibExt.GroupTheory.GroupLawsShared

/-- Kourovka 5.51 (D. M. Smirnov): the quasi-identities of a non-abelian free group (`FreeGroup α`
with at least two generators) have an independent basis. -/
def nonAbelianFreeGroupQuasiIdentitiesIndependentBasis : Prop :=
  ∀ α : Type, (∃ a b : α, a ≠ b) → HasIndependentQuasiIdentityBasis (FreeGroup α)

/--
Resolved true: the Kourovka Archive answers 5.51 "Yes, it does", citing Budkin, Independent
axiomatizability of quasivarieties of groups (Math. Notes 31 (1982), 413-417). Source: E. I. Khukhro
and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.51 (D. M. Smirnov); resolution: A.
I. Budkin, Independent axiomatizability of quasivarieties of groups, Math. Notes 31 (1982), 413-417,
Kourovka Archive, Problem 5.51: Yes, it does (Budkin), https://doi.org/10.1007/BF01372348.
-/
public theorem_wanted nonAbelianFreeGroupQuasiIdentitiesIndependentBasis_holds :
    nonAbelianFreeGroupQuasiIdentitiesIndependentBasis

end MathlibExt.GroupTheory.QuasiIdentityBasisFreeGroupKourovka5Problem51Wanted
