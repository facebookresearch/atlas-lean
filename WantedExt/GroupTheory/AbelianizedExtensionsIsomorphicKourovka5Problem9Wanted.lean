/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Abelianized extensions of minimal-plus-one presentations (Kourovka Notebook Problem 5.9)

Kourovka Notebook, Archive of Solved Problems, Problem 5.9 (K. W. Gruenberg): let 1 → Rᵢ → F → G →
1, i = 1, 2, be two exact sequences of groups with G finite and F free of finite rank d(F). If we
assume that d(F) = d(G) + 1 (where d(G) is the minimum number of generators of G), are the
corresponding abelianized extensions isomorphic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Rank

@[expose] public section

namespace MathlibExt.GroupTheory.AbelianizedExtensionsIsomorphicKourovka5Problem9Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.9 (K. W.
Gruenberg). UnsolvedMath record UM-00700293 (`KOU-5.9`), dataset ulamai/UnsolvedMath v1.8.0.

`d(G)` is Mathlib's `Group.rank G`, so `F = FreeGroup (Fin (Group.rank G + 1))`, and `Rᵢ = ker πᵢ`
for the two surjections `πᵢ : F →* G`. The abelianized extension of `πᵢ` is `Rᵢ ⧸ [Rᵢ, Rᵢ] ↣ F ⧸
[Rᵢ, Rᵢ] ↠ G`. Two extensions are taken to be isomorphic when an isomorphism `θ : F ⧸ [R₁, R₁] ≃* F
⧸ [R₂, R₂]` covers some automorphism `γ` of `G` (it then maps `R₁ ⧸ [R₁, R₁]` onto `R₂ ⧸ [R₂, R₂]`);
the compatibility is stated on representatives. This is the weakest standard notion; the version
with `γ = id` is stronger and not stated here, since Linnell's paper was not available to fix the
notion it uses.
-/

/-- Kourovka 5.9 (K. W. Gruenberg): let `G` be finite and `π₁, π₂ : F → G` surjections from a free
group of rank `d(G) + 1`, with kernels `R₁`, `R₂`. Then the abelianized extensions
`R_i ⧸ [R_i, R_i] ↣ F ⧸ [R_i, R_i] ↠ G` are isomorphic: some isomorphism
`θ : F ⧸ [R₁, R₁] ≃* F ⧸ [R₂, R₂]` covers an automorphism `γ` of `G`. -/
def abelianizedExtensionsIsomorphic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (π₁ π₂ : FreeGroup (Fin (Group.rank G + 1)) →* G),
    Function.Surjective π₁ → Function.Surjective π₂ →
    ∃ (θ : FreeGroup (Fin (Group.rank G + 1)) ⧸ ⁅π₁.ker, π₁.ker⁆ ≃*
        FreeGroup (Fin (Group.rank G + 1)) ⧸ ⁅π₂.ker, π₂.ker⁆) (γ : G ≃* G),
      ∀ w₁ w₂ : FreeGroup (Fin (Group.rank G + 1)),
        θ (QuotientGroup.mk w₁) = QuotientGroup.mk w₂ → γ (π₁ w₁) = π₂ w₂

/--
Resolved true: the Kourovka Archive answers 5.9 "Yes, they are", citing Linnell (1981): for a finite
group `G` and two surjections from a free group of rank `d(G) + 1`, the abelianized extensions are
isomorphic. Stated here in the weakest form, an isomorphism `F ⧸ [R₁, R₁] ≃* F ⧸ [R₂, R₂]` covering
an automorphism of `G`, which any of the standard notions of isomorphic extensions implies. Source:
E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook,
21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 5.9 (K. W. Gruenberg);
resolution: P. A. Linnell, Relation modules and augmentation ideals of finite groups, J. Pure Appl.
Algebra 22 (1981), 143-164 (the Archive prints 143-166), Kourovka Archive, Problem 5.9: Yes, they
are (Linnell), https://doi.org/10.1016/0022-4049(81)90056-6.
-/
public theorem_wanted abelianizedExtensionsIsomorphic_holds : abelianizedExtensionsIsomorphic

end MathlibExt.GroupTheory.AbelianizedExtensionsIsomorphicKourovka5Problem9Wanted
