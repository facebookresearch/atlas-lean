/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Categorical kernels in `GrpCat`

The categorical kernel of `f : G ⟶ H` is `f.hom.ker`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace GrpCat

instance {G H : GrpCat.{u}} : Zero (G ⟶ H) where
  zero := GrpCat.ofHom (1 : G →* H)

instance : HasZeroMorphisms GrpCat where
  comp_zero {X Y} f Z := by
    ext x
    change (1 : Y →* Z) (f x) = (1 : X →* Z) x
    rfl
  zero_comp X {Y Z} f := by
    ext x
    change f ((1 : X →* Y) x) = (1 : X →* Z) x
    simp [map_one]

/-- The categorical kernel of a morphism in `GrpCat`
agrees with the usual group-theoretic kernel. -/
noncomputable def kernelIsoKer {G H : GrpCat.{u}} (f : G ⟶ H) :
    Limits.kernel f ≅ GrpCat.of f.hom.ker where
  hom := GrpCat.ofHom
    { toFun := fun g =>
        ⟨Limits.kernel.ι f g, by
          have h := ConcreteCategory.congr_hom (Limits.kernel.condition (C := GrpCat) f) g
          dsimp [Zero.zero, GrpCat.hom_comp] at h ⊢
          exact h⟩
      map_one' := by
        refine Subtype.ext ?_
        simp
      map_mul' := fun g g' => by
        refine Subtype.ext ?_
        simp }
  inv := Limits.kernel.lift f (GrpCat.ofHom (Subgroup.subtype f.hom.ker)) <| by
    ext x
    change f.hom ↑x = 1
    exact x.2
  hom_inv_id := by
    refine CategoryTheory.Limits.equalizer.hom_ext ?_
    ext x
    simp
  inv_hom_id := by
    apply GrpCat.ext
    rintro ⟨x, hx⟩
    refine Subtype.ext ?_
    apply ConcreteCategory.congr_hom (Limits.kernel.lift_ι f _ _)

@[simp]
theorem kernelIsoKer_hom_comp_subtype {G H : GrpCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).hom ≫ GrpCat.ofHom (Subgroup.subtype f.hom.ker) = Limits.kernel.ι f := by
  ext x
  rfl

@[simp]
theorem kernelIsoKer_inv_comp_ι {G H : GrpCat.{u}} (f : G ⟶ H) :
    (kernelIsoKer f).inv ≫ Limits.kernel.ι f = GrpCat.ofHom (Subgroup.subtype f.hom.ker) := by
  simp [kernelIsoKer]

end GrpCat
