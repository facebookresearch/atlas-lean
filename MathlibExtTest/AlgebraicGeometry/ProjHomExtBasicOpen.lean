/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjHomExtBasicOpen

@[expose] public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

universe u v

theorem exactSource
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
    a = b :=
  AlgebraicGeometry.Proj.hom_ext_of_forall_exists_basicOpen 𝒜 a b h
