/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen.lean`
and
`P2M/Sol/S_AlgebraicGeometry_Proj_hom_ext_of_forall_exists_basicOpen.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Restrict

@[expose] public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u v

namespace AlgebraicGeometry

/-- Two morphisms into `Proj 𝒜` are equal if, at every point of the source,
some homogeneous basic open of positive degree contains the image point, the
two preimages of that basic open agree, and the two morphisms agree on all
sections coming from the degree-zero part of the localization away from the
defining element. -/
theorem Proj.hom_ext_of_forall_exists_basicOpen
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {W : Scheme.{u}} (a b : W ⟶ Proj 𝒜)
    (h : ∀ w : W, ∃ (n : ℕ) (r : A) (hn : 0 < n) (hr : r ∈ 𝒜 n)
      (e : a ⁻¹ᵁ Proj.basicOpen 𝒜 r = b ⁻¹ᵁ Proj.basicOpen 𝒜 r),
      w ∈ a ⁻¹ᵁ Proj.basicOpen 𝒜 r ∧
        ∀ x : Away 𝒜 r,
          a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl
              (Proj.awayToSection 𝒜 r x) =
            b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le
              (Proj.awayToSection 𝒜 r x)) :
    a = b := by
  refine Scheme.hom_ext_of_forall a b fun w => ?_
  obtain ⟨n, r, hn, hr, e, hw, happ⟩ := h w
  refine ⟨a ⁻¹ᵁ Proj.basicOpen 𝒜 r, hw, ?_⟩
  have hsurj : Function.Surjective (Proj.awayToSection 𝒜 r) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒜 r hr hn]
    exact (ConcreteCategory.bijective_of_isIso _).2
  have happLE : a.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl =
      b.appLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le := by
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    exact happ y
  have key : a.resLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl =
      b.resLE (Proj.basicOpen 𝒜 r) (a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le := by
    haveI : IsAffine (Proj.basicOpen 𝒜 r).toScheme :=
      Proj.isAffineOpen_basicOpen 𝒜 r hr hn
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, happLE]
  have e₁ := Scheme.Hom.resLE_comp_ι a (U := Proj.basicOpen 𝒜 r)
    (V := a ⁻¹ᵁ Proj.basicOpen 𝒜 r) le_rfl
  have e₂ := Scheme.Hom.resLE_comp_ι b (U := Proj.basicOpen 𝒜 r)
    (V := a ⁻¹ᵁ Proj.basicOpen 𝒜 r) e.le
  rw [← e₁, ← e₂, key]

end AlgebraicGeometry
