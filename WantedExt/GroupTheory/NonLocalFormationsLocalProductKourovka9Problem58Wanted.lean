/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local products of non-local formations (Kourovka Notebook Problem 9.58)

Kourovka Notebook, Archive of Solved Problems, Problem 9.58 (A. N. Skiba and L. A. Shemetkov): can a
product of non-local formations of finite groups be local?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.FiniteGroupFormationShared

@[expose] public section

namespace MathlibExt.GroupTheory.NonLocalFormationsLocalProductKourovka9Problem58Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.58 (A. N.
Skiba and L. A. Shemetkov). UnsolvedMath record UM-00700591 (`KOU-9.58`), dataset
ulamai/UnsolvedMath v1.8.0.

Formations of finite groups are `FiniteGroupClass` predicates with `IsFormation` from the 13.51
entry (closed under homomorphic images and finite subdirect products). "Local" is the shared
`FiniteGroupFormationShared.IsLocalFormation`: a formation containing the trivial group that is
saturated (`G / Φ(G) ∈ 𝔉 → G ∈ 𝔉`); by the Gaschütz-Lubeseder-Schmid theorem a non-empty formation
of finite groups is local iff it is saturated. The product `𝔉𝔊` is Gaschütz's: `G ∈ 𝔉𝔊` iff the
`𝔊`-residual `G^𝔊` (the intersection of the normal subgroups `N` with `G/N ∈ 𝔊`) lies in `𝔉`. Both
factors are required to contain the trivial group (formations are non-empty), so they are non-local
exactly when they are not saturated.
-/

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
open MathlibExt.GroupTheory.FiniteGroupFormationShared


/-- The product `𝔉𝔊` of classes of finite groups: `G ∈ 𝔉𝔊` iff the `𝔊`-residual of `G` lies in
`𝔉`. -/
def formationProduct (𝔉 𝔊 : FiniteGroupClass) : FiniteGroupClass :=
  fun G _ _ => 𝔉 (residual 𝔊 G)

/-- Kourovka 9.58 (A. N. Skiba, L. A. Shemetkov): there are non-local formations `𝔉` and `𝔊` of
finite groups (formations containing the trivial group) whose product `𝔉𝔊` is local. -/
def existsNonLocalFormationsLocalProduct : Prop :=
  ∃ 𝔉 𝔊 : FiniteGroupClass, IsFormation 𝔉 ∧ 𝔉 Unit ∧ ¬ IsLocalFormation 𝔉 ∧
    IsFormation 𝔊 ∧ 𝔊 Unit ∧ ¬ IsLocalFormation 𝔊 ∧ IsLocalFormation (formationProduct 𝔉 𝔊)

/--
Resolved true: the Kourovka Archive answers 9.58 "Yes, it can", citing Vedernikov's paper on local
formations and Vorob'ev: there are non-local formations `𝔉`, `𝔊` of finite groups whose product `𝔉𝔊`
is local. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.58
(A. N. Skiba and L. A. Shemetkov); resolution: V. A. Vedernikov, Local formations of finite groups,
Math. Notes 46 (1989), 910-913; N. T. Vorob'ev, in: Proc. 7th Regional Sci. Session Math., Zielona
Góra, 1989, 79-86, zbMATH review Zbl 0729.20010 of Vedernikov's paper: an affirmative answer to
Question 9.58; Kourovka Archive of Solved Problems, Problem 9.58: Yes, it can,
https://doi.org/10.1007/BF01158624.
-/
public theorem_wanted existsNonLocalFormationsLocalProduct_holds :
    existsNonLocalFormationsLocalProduct

end MathlibExt.GroupTheory.NonLocalFormationsLocalProductKourovka9Problem58Wanted
