/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module
public import MathlibExt.CategoryTheory.Monoidal.Mod.Closed

/-!
# Original evaluation and coevaluation components for relative tensor

The equations below describe the actual evaluation and coevaluation used by
the original relative tensor adjunction. The balanced projection and the
complete action equalizer inclusion remain the maps of that construction.
The two triangle equations recover the entire original modules.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.MonObj

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]
  (A : CommMon C) [HasCoequalizers C] [HasEqualizers C]

/-- The whole original balanced evaluation is uncurrying the full equalizer inclusion. -/
@[reassoc]
theorem evaluation_π (M N : Mod C A.X) :
    relativeTensorπ A M ((internalHomOfEqualizer A M).obj N) ≫
        ((evaluation A M).app N).hom =
      MonoidalClosed.uncurry (internalHomι A M N) := by
  dsimp [evaluation]
  apply relativeTensorDesc_π

/-- The original coevaluation retains the complete balanced projection after inclusion. -/
@[reassoc]
theorem coevaluation_ι (M N : Mod C A.X) :
    ((coevaluation A M).app N).hom ≫
        internalHomι A M (((relativeTensor A).obj M).obj N) =
      MonoidalClosed.curry (relativeTensorπ A M N) := by
  let T := ((relativeTensor A).obj M).obj N
  let π : M.X ⊗ N.X ⟶ T.X := relativeTensorπ A M N
  let k : N.X ⟶ (ihom M.X).obj T.X := MonoidalClosed.curry π
  have hπlinear : (A.X ◁ π) ≫ T.mod.smul =
      (α_ A.X M.X N.X).inv ≫ (M.mod.smul ▷ N.X) ≫ π := by
    dsimp only [T, π]
    exact Bimod.TensorBimod.whiskerLeft_π_actLeft
      (C := C) (R := A.toMon) (S := A.toMon) (T := A.toMon) _ _
  have hpre : MonoidalClosed.uncurry
        (k ≫ internalHomPre A M T) =
      (M.mod.smul ▷ N.X) ≫ π := by
    dsimp only [internalHomPre]
    rw [MonoidalClosed.uncurry_pre_app]
    dsimp only [k]
    rw [MonoidalClosed.uncurry_curry]
  have hpost : MonoidalClosed.uncurry
        (k ≫ internalHomPost A M T) =
      (α_ A.X M.X N.X).hom ≫ (A.X ◁ π) ≫ T.mod.smul := by
    rw [MonoidalClosed.uncurry_natural_left]
    dsimp only [internalHomPost]
    rw [MonoidalClosed.uncurry_curry]
    dsimp only [k]
    slice_lhs 1 2 => rw [associator_naturality_right]
    slice_lhs 2 3 => rw [← whiskerLeft_comp,
      MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  have hfork : k ≫ internalHomPre A M T =
      k ≫ internalHomPost A M T := by
    apply MonoidalClosed.uncurry_injective
    rw [hpre, hpost, hπlinear]
    simp only [Iso.hom_inv_id_assoc]
  have happ : ((coevaluation A M).app N).hom =
      Fork.IsLimit.lift (internalHomIsLimit A M T) k hfork := by
    unfold coevaluation
    rfl
  rw [happ]
  exact Fork.IsLimit.lift_ι' (internalHomIsLimit A M T) k hfork

omit [HasEqualizers C] in
/-- Every whole tensor-variable module map retains its actual quotient projection. -/
@[reassoc]
theorem relativeTensor_map_π (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') :
    relativeTensorπ A M N ≫ (((relativeTensor A).obj M).map g).hom =
      (M.X ◁ g.hom) ≫ relativeTensorπ A M N' := by
  let _ : MonoidalCategory (Mod C A.X) := instMonoidalCategory A
  have hmap : relativeTensorMap A (𝟙 M) g =
      ((relativeTensor A).obj M).map g := by
    change (𝟙 M) ⊗ₘ g = M ◁ g
    exact id_tensorHom M g
  rw [← hmap, relativeTensorMap_π]
  simp only [Mod.id_hom', tensorHom_def, id_whiskerRight, Category.id_comp]

/-- The actual unit is the whole original coevaluation natural transformation. -/
theorem relativeTensorInternalHomAdjunction_unit (M : Mod C A.X) :
    (relativeTensorInternalHomAdjunction A M).unit = coevaluation A M := rfl

/-- The actual counit is the whole original balanced evaluation natural transformation. -/
theorem relativeTensorInternalHomAdjunction_counit (M : Mod C A.X) :
    (relativeTensorInternalHomAdjunction A M).counit = evaluation A M := rfl

/-- Every original unit component keeps the full balanced tensor projection. -/
@[reassoc]
theorem relativeTensorInternalHomAdjunction_unit_ι (M N : Mod C A.X) :
    ((relativeTensorInternalHomAdjunction A M).unit.app N).hom ≫
        internalHomι A M (((relativeTensor A).obj M).obj N) =
      MonoidalClosed.curry (relativeTensorπ A M N) := by
  rw [relativeTensorInternalHomAdjunction_unit]
  exact coevaluation_ι A M N

/-- Every original counit component is the complete balanced equalizer evaluation. -/
@[reassoc]
theorem relativeTensorInternalHomAdjunction_counit_π (M N : Mod C A.X) :
    relativeTensorπ A M ((internalHomOfEqualizer A M).obj N) ≫
        ((relativeTensorInternalHomAdjunction A M).counit.app N).hom =
      MonoidalClosed.uncurry (internalHomι A M N) := by
  rw [relativeTensorInternalHomAdjunction_counit]
  exact evaluation_π A M N

/-- The actual unit and counit recover the whole original balanced tensor module. -/
theorem relativeTensorInternalHomAdjunction_left_triangle (M N : Mod C A.X) :
    ((relativeTensor A).obj M).map
        ((relativeTensorInternalHomAdjunction A M).unit.app N) ≫
      (relativeTensorInternalHomAdjunction A M).counit.app
        (((relativeTensor A).obj M).obj N) =
      𝟙 (((relativeTensor A).obj M).obj N) :=
  (relativeTensorInternalHomAdjunction A M).left_triangle_components N

/-- The actual unit and counit recover the whole original action equalizer module. -/
theorem relativeTensorInternalHomAdjunction_right_triangle (M N : Mod C A.X) :
    (relativeTensorInternalHomAdjunction A M).unit.app ((internalHomOfEqualizer A M).obj N) ≫
      (internalHomOfEqualizer A M).map
        ((relativeTensorInternalHomAdjunction A M).counit.app N) =
      𝟙 ((internalHomOfEqualizer A M).obj N) :=
  (relativeTensorInternalHomAdjunction A M).right_triangle_components N

end CategoryTheory.Mod
