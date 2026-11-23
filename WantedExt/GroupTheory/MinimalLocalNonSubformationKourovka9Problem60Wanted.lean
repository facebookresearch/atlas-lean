/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Minimal local non-H-subformations (Kourovka Notebook Problem 9.60)

Kourovka Notebook, Archive of Solved Problems, Problem 9.60 (A. N. Skiba and L. A. Shemetkov): let
`𝔉` and `𝔊` be local formations of finite groups and suppose that `𝔉` is not contained in `𝔊`. Does
`𝔉` necessarily have at least one minimal local non-`𝔊`-subformation?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.GroupTheory.FiniteGroupFormationShared

@[expose] public section

namespace MathlibExt.GroupTheory.MinimalLocalNonSubformationKourovka9Problem60Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.60 (A. N.
Skiba and L. A. Shemetkov). UnsolvedMath record UM-00700593 (`KOU-9.60`), dataset
ulamai/UnsolvedMath v1.8.0.

Formations of finite groups are `FiniteGroupClass` predicates with `IsFormation` from the 13.51
entry (closed under homomorphic images and finite subdirect products). "Local" is the shared
`FiniteGroupFormationShared.IsLocalFormation`: a formation containing the trivial group that is
saturated (`G / Φ(G) ∈ 𝔉 → G ∈ 𝔉`); by the Gaschütz-Lubeseder-Schmid theorem a non-empty formation
of finite groups is local iff it is saturated. A minimal local non-`𝔊`-subformation of `𝔉` is a
local formation `𝔐 ⊆ 𝔉` with `𝔐 ⊄ 𝔊` all of whose proper local subformations are contained in `𝔊`.
-/

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
open MathlibExt.GroupTheory.FiniteGroupFormationShared


/-- `𝔐` is a minimal local non-`𝔊`-subformation of `𝔉`: a local subformation of `𝔉` not contained in
`𝔊` all of whose proper local subformations are contained in `𝔊`. -/
def IsMinimalLocalNonSubformation (𝔐 𝔉 𝔊 : FiniteGroupClass) : Prop :=
  IsLocalFormation 𝔐 ∧ ClassLE 𝔐 𝔉 ∧ ¬ ClassLE 𝔐 𝔊 ∧
    ∀ 𝔏 : FiniteGroupClass, IsLocalFormation 𝔏 → ClassLE 𝔏 𝔐 → ¬ ClassLE 𝔐 𝔏 → ClassLE 𝔏 𝔊

/-- Kourovka 9.60 (A. N. Skiba, L. A. Shemetkov): if `𝔉` and `𝔊` are local formations of finite
groups and `𝔉 ⊄ 𝔊`, then `𝔉` has a minimal local non-`𝔊`-subformation. -/
def minimalLocalNonSubformationExists : Prop :=
  ∀ 𝔉 𝔊 : FiniteGroupClass, IsLocalFormation 𝔉 → IsLocalFormation 𝔊 → ¬ ClassLE 𝔉 𝔊 →
    ∃ 𝔐 : FiniteGroupClass, IsMinimalLocalNonSubformation 𝔐 𝔉 𝔊

/--
Resolved false: the Kourovka Archive answers 9.60 "No, not necessarily", citing Burichenko, who
describes local formations `𝔉`, `𝔊` such that the set of local formations contained in `𝔉` and not
contained in `𝔊` has no minimal element (zbMATH review Zbl 1459.20012), so `𝔉` has no minimal local
non-`𝔊`-subformation. Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 9.60 (A. N. Skiba and L. A. Shemetkov); resolution: V. P. Burichenko, Some finiteness
questions about formations, Trudy Inst. Mat. (Minsk) 21 (2013), no. 1, 15-24 (Russian), summary in
the zbMATH review Zbl 1459.20012: a pair of local formations (𝔉, ℌ) such that the set of all local
formations contained in 𝔉 and not contained in ℌ has no minimal element; Kourovka Archive of Solved
Problems, Problem 9.60: No, not necessarily, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted minimalLocalNonSubformationExists_refuted :
    ¬ minimalLocalNonSubformationExists

end MathlibExt.GroupTheory.MinimalLocalNonSubformationKourovka9Problem60Wanted
