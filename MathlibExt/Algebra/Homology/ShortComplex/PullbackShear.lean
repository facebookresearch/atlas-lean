/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ShortComplex.Pullback
public import MathlibExt.CategoryTheory.Limits.Shapes.PullbackShear

/-!
# Additive shears of pullback short complexes

If `a ≫ S.g = f - g`, the pullbacks `S.pull f` and `S.pull g` are
isomorphic. The first and last components are identities; the middle
component subtracts `fst ≫ a` from the second projection, and its inverse
adds it. The construction uses preadditivity and the two specified pullbacks.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (S : ShortComplex C) {X : C} (f g : X ⟶ S.X₃) (a : X ⟶ S.X₂)
  (ha : a ≫ S.g = f - g) [HasPullback f S.g] [HasPullback g S.g]

/-- The pullback shear fixes the first and last objects of a native
short complex. -/
def pullShearIso : S.pull f ≅ S.pull g :=
  ShortComplex.isoMk (Iso.refl S.X₁) (pullback.shearIso S.g f g a ha) (Iso.refl X)
    (by
      change (𝟙 S.X₁) ≫ (S.pull g).f =
        (S.pull f).f ≫ pullback.shearHom S.g f g a ha
      rw [Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.shearHom_fst]
        simp only [ShortComplex.pull_f, pullback.lift_fst]
      · rw [Category.assoc, pullback.shearHom_snd, Preadditive.comp_sub]
        simp only [ShortComplex.pull_f, pullback.lift_snd]
        rw [← Category.assoc, pullback.lift_fst, zero_comp, sub_zero])
    (by
      change pullback.shearHom S.g f g a ha ≫ (S.pull g).g = (S.pull f).g ≫ 𝟙 X
      simp only [ShortComplex.pull_g, pullback.shearHom_fst]
      exact (Category.comp_id (pullback.fst f S.g)).symm)

@[simp]
theorem pullShearIso_hom_τ₁ : (pullShearIso S f g a ha).hom.τ₁ = 𝟙 S.X₁ :=
  rfl

@[simp]
theorem pullShearIso_hom_τ₃ : (pullShearIso S f g a ha).hom.τ₃ = 𝟙 X :=
  rfl

@[simp]
theorem pullShearIso_inv_τ₁ : (pullShearIso S f g a ha).inv.τ₁ = 𝟙 S.X₁ :=
  rfl

@[simp]
theorem pullShearIso_inv_τ₃ : (pullShearIso S f g a ha).inv.τ₃ = 𝟙 X :=
  rfl

@[reassoc (attr := simp)]
theorem pullShearIso_hom_τ₂_fst :
    (pullShearIso S f g a ha).hom.τ₂ ≫ pullback.fst g S.g = pullback.fst f S.g := by
  change pullback.shearHom S.g f g a ha ≫ pullback.fst g S.g = pullback.fst f S.g
  exact pullback.shearHom_fst S.g f g a ha

@[reassoc (attr := simp)]
theorem pullShearIso_hom_τ₂_snd :
    (pullShearIso S f g a ha).hom.τ₂ ≫ pullback.snd g S.g =
      pullback.snd f S.g - pullback.fst f S.g ≫ a := by
  change pullback.shearHom S.g f g a ha ≫ pullback.snd g S.g = _
  exact pullback.shearHom_snd S.g f g a ha

@[reassoc (attr := simp)]
theorem pullShearIso_inv_τ₂_fst :
    (pullShearIso S f g a ha).inv.τ₂ ≫ pullback.fst f S.g = pullback.fst g S.g := by
  change pullback.shearInv S.g f g a ha ≫ pullback.fst f S.g = pullback.fst g S.g
  exact pullback.shearInv_fst S.g f g a ha

@[reassoc (attr := simp)]
theorem pullShearIso_inv_τ₂_snd :
    (pullShearIso S f g a ha).inv.τ₂ ≫ pullback.snd f S.g =
      pullback.snd g S.g + pullback.fst g S.g ≫ a := by
  change pullback.shearInv S.g f g a ha ≫ pullback.snd f S.g = _
  exact pullback.shearInv_snd S.g f g a ha

end CategoryTheory.ShortComplex
