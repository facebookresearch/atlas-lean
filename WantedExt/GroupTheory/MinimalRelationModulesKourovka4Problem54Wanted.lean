/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Non-isomorphic minimal relation modules (Kourovka Notebook Problem 4.54)

Kourovka Notebook, Archive of Solved Problems, Problem 4.54 (K. W. Roggenkamp): are any two minimal
relation-modules of a finite group isomorphic?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Rank

@[expose] public section

namespace MathlibExt.GroupTheory.MinimalRelationModulesKourovka4Problem54Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.54 (K. W.
Roggenkamp). UnsolvedMath record UM-00700261 (`KOU-4.54`), dataset ulamai/UnsolvedMath v1.8.0.

A minimal relation module of a finite group `G` is `R/[R, R]` for a presentation `1 → R → F → G → 1`
with `F` free of rank `d(G)` (Mathlib's `Group.rank G`, the minimal number of generators), with `G`
acting by conjugation (`g = π(u)` acts through conjugation by `u`, well defined because `R` acts
trivially on `R/[R, R]`). Two such modules are isomorphic as `ℤG`-modules when an isomorphism of the
abelian groups `Abelianization R₁ ≃ Abelianization R₂` intertwines the two actions.
-/

/-- The relation modules `R₁/[R₁, R₁]` and `R₂/[R₂, R₂]` of two presentations
`π₁, π₂ : F_d → G` (`Rᵢ = ker πᵢ`) are isomorphic as `ℤG`-modules: some isomorphism of the
abelianizations intertwines the conjugation actions of `G`, where `g = π₁(u₁) = π₂(u₂)` acts on
`Rᵢ/[Rᵢ, Rᵢ]` through conjugation by `uᵢ`. -/
def RelationModulesIsomorphic {G : Type*} [Group G] {d : ℕ} (π₁ π₂ : FreeGroup (Fin d) →* G) :
    Prop :=
  ∃ f : Abelianization π₁.ker ≃* Abelianization π₂.ker,
    ∀ u₁ u₂ : FreeGroup (Fin d), π₁ u₁ = π₂ u₂ → ∀ m : Abelianization π₁.ker,
      f (Abelianization.map (MulAut.conjNormal u₁ : π₁.ker ≃* π₁.ker).toMonoidHom m) =
        Abelianization.map (MulAut.conjNormal u₂ : π₂.ker ≃* π₂.ker).toMonoidHom (f m)

/-- Kourovka 4.54 (K. W. Roggenkamp): any two minimal relation modules of a finite group `G` are
isomorphic: for any two presentations `1 → Rᵢ → F → G → 1` with `F` free of rank `d(G)`, the
minimal number of generators of `G`, the `ℤG`-modules `Rᵢ/[Rᵢ, Rᵢ]` are isomorphic. -/
def minimalRelationModulesIsomorphic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (π₁ π₂ : FreeGroup (Fin (Group.rank G)) →* G),
    Function.Surjective π₁ → Function.Surjective π₂ → RelationModulesIsomorphic π₁ π₂

/--
Resolved false: Linnell and Sieradski-Dyer exhibit finite groups with non-isomorphic minimal
relation modules; the Kourovka Archive answers 4.54 "Not always". Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 4.54 (K. W. Roggenkamp); resolution:
P. A. Linnell, Ph. D. Thesis, Cambridge, 1979; A. J. Sieradski and M. N. Dyer, Distinguishing
arithmetic for certain stably isomorphic modules, J. Pure Appl. Algebra 15 (1979), 199-217, Kourovka
Archive of Solved Problems, Problem 4.54: Not always, https://doi.org/10.1016/0022-4049(79)90034-3.
-/
public theorem_wanted minimalRelationModulesIsomorphic_refuted : ¬ minimalRelationModulesIsomorphic

end MathlibExt.GroupTheory.MinimalRelationModulesKourovka4Problem54Wanted
