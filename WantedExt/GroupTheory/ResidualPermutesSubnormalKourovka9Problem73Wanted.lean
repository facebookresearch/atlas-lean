/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Residuals of subnormal subgroups permute (Kourovka Notebook Problem 9.73)

Kourovka Notebook, Archive of Solved Problems, Problem 9.73 (L. A. Shemetkov): let `𝔉` be any local
formation of finite soluble groups containing all finite nilpotent groups. Prove that `H^𝔉 K = K
H^𝔉` for any two subnormal subgroups `H` and `K` of an arbitrary finite group `G`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.IsSubnormal
public import WantedExt.GroupTheory.FiniteGroupFormationShared

@[expose] public section

namespace MathlibExt.GroupTheory.ResidualPermutesSubnormalKourovka9Problem73Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 9.73 (L. A.
Shemetkov). UnsolvedMath record UM-00700606 (`KOU-9.73`), dataset ulamai/UnsolvedMath v1.8.0.

Formations of finite groups are `FiniteGroupClass` predicates with `IsFormation` from the 13.51
entry (closed under homomorphic images and finite subdirect products). "Local" is the shared
`FiniteGroupFormationShared.IsLocalFormation`: a formation containing the trivial group that is
saturated (`G / Φ(G) ∈ 𝔉 → G ∈ 𝔉`); by the Gaschütz-Lubeseder-Schmid theorem a non-empty formation
of finite groups is local iff it is saturated. `H^𝔉` is the `𝔉`-residual of `H` (shared `residual`),
mapped into `G`. The Archive states that the result holds even without the solubility of `𝔉`, and
that stronger statement, Kamornikov's theorem, is formalized (it contains the one asked).
-/

open MathlibExt.GroupTheory.FiniteModularLatticeFormationsKourovka13Problem51Wanted
open MathlibExt.GroupTheory.FiniteGroupFormationShared
open scoped Pointwise


/-- Kourovka 9.73 (L. A. Shemetkov), in the form proved by Kamornikov (without solubility of `𝔉`):
for every local formation `𝔉` of finite groups containing all finite nilpotent groups, every finite
group `G` and subnormal subgroups `H`, `K` of `G`, the `𝔉`-residual `H^𝔉` of `H` permutes with `K`:
`H^𝔉 K = K H^𝔉`. -/
def residualPermutesSubnormal : Prop :=
  ∀ 𝔉 : FiniteGroupClass, IsLocalFormation 𝔉 →
    (∀ (N : Type) [Group N] [Finite N], Group.IsNilpotent N → 𝔉 N) →
    ∀ (G : Type) [Group G] [Finite G] (H K : Subgroup G), H.IsSubnormal → K.IsSubnormal →
      (((residual 𝔉 H).map H.subtype : Subgroup G) : Set G) * (K : Set G) =
        (K : Set G) * (((residual 𝔉 H).map H.subtype : Subgroup G) : Set G)

/--
Resolved true: Kamornikov proves that for a local formation `𝔉` of finite groups containing all
finite nilpotent groups, `H^𝔉 K = K H^𝔉` for any two subnormal subgroups `H`, `K` of a finite group
(summary in the zbMATH review Zbl 0692.20014); the Kourovka Archive records 9.73 as proved, even
without the hypothesis that `𝔉` consists of soluble groups. Source: E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(2026), Archive of Solved Problems, Problem 9.73 (L. A. Shemetkov); resolution: S. F. Kamornikov,
Permutable subnormal subgroups of finite groups, Dokl. Akad. Nauk BSSR 33 (1989), no. 5, 396-399
(Russian), summary in the zbMATH review Zbl 0692.20014: for a local formation 𝔉 of finite groups
containing all finite nilpotent groups, H^𝔉 K = K H^𝔉 for any two subnormal subgroups H and K of a
finite group; Kourovka Archive of Solved Problems, Problem 9.73: This has been proved, even without
the hypothesis of solubility of 𝔉, https://arxiv.org/abs/1401.0300v49.
-/
public theorem_wanted residualPermutesSubnormal_holds : residualPermutesSubnormal

end MathlibExt.GroupTheory.ResidualPermutesSubnormalKourovka9Problem73Wanted
