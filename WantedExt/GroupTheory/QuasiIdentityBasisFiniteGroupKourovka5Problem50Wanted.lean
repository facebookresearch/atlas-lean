/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A finite group whose quasi-identities have no independent basis (Kourovka Notebook Problem 5.50)

Kourovka Notebook, Archive of Solved Problems, Problem 5.50 (D. M. Smirnov): is there a finite group
whose set of quasi-laws does not have an independent basis?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Finite.Defs
public import WantedExt.GroupTheory.GroupLawsShared

@[expose] public section

namespace MathlibExt.GroupTheory.QuasiIdentityBasisFiniteGroupKourovka5Problem50Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.50 (D. M.
Smirnov). UnsolvedMath record UM-00700331 (`KOU-5.50`), dataset ulamai/UnsolvedMath v1.8.0.

Quasi-laws are the quasi-identities `∀ x, (u₁ = 1 ∧ ⋯ ∧ uₖ = 1 → w = 1)` holding in the group
(`QuasiIdentity` of the Kourovka 14.25 entry, reused here: premises and conclusion in a free group
of finite rank), with consequence and independent bases as in the shared module
`WantedExt.GroupTheory.GroupLawsShared`: a basis is a set of quasi-identities whose consequences are
exactly the quasi-laws of `G`, independent when none of its members is a consequence of the others.
-/

open MathlibExt.GroupTheory.GroupLawsShared

/-- Kourovka 5.50 (D. M. Smirnov): there is a finite group whose quasi-identities have no
independent basis. -/
def existsFiniteGroupQuasiIdentitiesNoIndependentBasis : Prop :=
  ∃ (G : Type) (_ : Group G) (_ : Finite G), ¬ HasIndependentQuasiIdentityBasis G

/--
Resolved true: the Kourovka Archive answers 5.50 "Yes, there is", citing Fedorov, Subquasivarieties
of nilpotent minimal non-Abelian group varieties (Siberian Math. J. 21 (1980), 840-850). Source: E.
I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st
issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.50 (D. M. Smirnov);
resolution: A. N. Fedorov, Subquasivarieties of nilpotent minimal non-Abelian group varieties,
Siberian Math. J. 21 (1980), 840-850, Kourovka Archive, Problem 5.50: Yes, there is (Fedorov),
https://doi.org/10.1007/BF00968471.
-/
public theorem_wanted existsFiniteGroupQuasiIdentitiesNoIndependentBasis_holds :
    existsFiniteGroupQuasiIdentitiesNoIndependentBasis

end MathlibExt.GroupTheory.QuasiIdentityBasisFiniteGroupKourovka5Problem50Wanted
