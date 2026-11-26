/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SeparatedPullbackDetection

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- Consumer with the original binders.
example (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X Y : Scheme.{u}) (fX : X ⟶ Spec (CommRingCat.of k))
    (fY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated fY]
    (g₁ g₂ : X ⟶ Y) (h₁ : g₁ ≫ fY = fX) (h₂ : g₂ ≫ fY = fX)
    (H : pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₁ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₁])
            (by rw [Category.comp_id, Category.id_comp]) =
         pullback.map fX (Spec.map (CommRingCat.ofHom (algebraMap k K))) fY
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            g₂ (𝟙 _) (𝟙 _) (by rw [Category.comp_id, h₂])
            (by rw [Category.comp_id, Category.id_comp])) :
    g₁ = g₂ :=
  AlgebraicGeometry.eq_of_pullback_map_eq_pullback_map_of_isSeparated k K X Y fX fY g₁ g₂
    h₁ h₂ H
