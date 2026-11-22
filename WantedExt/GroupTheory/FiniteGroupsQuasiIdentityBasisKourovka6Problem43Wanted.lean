/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Bases of the quasi-identities of finite groups (Kourovka Notebook Problem 6.43)

Kourovka Notebook, Archive of Solved Problems, Problem 6.43 (D. M. Smirnov): does the set of
quasi-identities holding in the class of all finite groups possess a basis in finitely many
variables?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.QuasivarietyMaximalSubquasivarietiesKourovka14Problem25Wanted

@[expose] public section

namespace MathlibExt.GroupTheory.FiniteGroupsQuasiIdentityBasisKourovka6Problem43Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.43 (D. M.
Smirnov). UnsolvedMath record UM-00700386 (`KOU-6.43`), dataset ulamai/UnsolvedMath v1.8.0.

Quasi-identities are `QuasiIdentity` of the Kourovka 14.25 module (premises and a conclusion, words
in `q.n` unknowns, each equation `u = v` written `u v⁻¹ = 1`). A basis in at most `m` variables is a
set `B` of quasi-identities in at most `m` unknowns, each true in all finite groups, such that every
group (in `Type`) satisfying `B` satisfies every quasi-identity true in all finite groups.
-/

open MathlibExt.GroupTheory.QuasivarietyMaximalSubquasivarietiesKourovka14Problem25Wanted
  (QuasiIdentity Models)

/-- Kourovka 6.43 (D. M. Smirnov): the quasi-identities holding in all finite groups have a basis in
finitely many variables: for some `m`, a set `B` of quasi-identities in at most `m` unknowns, each
holding in all finite groups, implies (in every group) every quasi-identity holding in all finite
groups. -/
def finiteGroupsQuasiIdentitiesBoundedVariableBasis : Prop :=
  ∃ (m : ℕ) (B : Set QuasiIdentity), (∀ q ∈ B, q.n ≤ m) ∧
    (∀ q ∈ B, ∀ (F : Type) [Group F] [Finite F], q.HoldsIn F) ∧
    ∀ (G : Type) [Group G], Models B G → ∀ q : QuasiIdentity,
      (∀ (F : Type) [Group F] [Finite F], q.HoldsIn F) → q.HoldsIn G

/--
Resolved false: the Kourovka Archive answers 6.43 "No", citing Rumyantsev (1980): the
quasi-identities holding in all finite groups have no basis in finitely many variables. Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 6.43 (D. M. Smirnov);
resolution: A. K. Rumyantsev, Quasiidentities of finite groups, Algebra and Logic 19 (1980),
297-311, Kourovka Archive, Problem 6.43: No (Rumyantsev), https://doi.org/10.1007/BF01674472.
-/
public theorem_wanted finiteGroupsQuasiIdentitiesBoundedVariableBasis_refuted :
    ¬ finiteGroupsQuasiIdentitiesBoundedVariableBasis

end MathlibExt.GroupTheory.FiniteGroupsQuasiIdentityBasisKourovka6Problem43Wanted
