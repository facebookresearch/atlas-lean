/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.InternalHom
public import MathlibExt.CategoryTheory.Monoidal.Mod.RelativeTensor

/-!
# Closed relative tensor products of internal modules

This file constructs evaluation and coevaluation for the balanced relative
tensor and the module internal Hom, proves the resulting adjunction, and packages
the explicit closed structure over the selected relative-tensor monoidal
structure.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
variable (A : CommMon C)
variable [HasCoequalizers C]
variable [HasEqualizers C]

/-- Evaluation of the module internal Hom on the balanced relative tensor. -/
noncomputable def evaluation (M : Mod C A.X) :
    internalHomOfEqualizer A M ⋙ (relativeTensor A).obj M ⟶ 𝟭 (Mod C A.X) := by
  let _ : CreatesLimitsOfShape WalkingParallelPair
      (Mod.forget (D := C) A.X) := by
    let _ := Mod.forgetCreatesLimits.{0} A.X
    infer_instance
  let _ : HasLimitsOfShape WalkingParallelPair (Mod C A.X) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (Mod.forget (D := C) A.X)
  let component (N : Mod C A.X) :
      ((relativeTensor A).obj M).obj ((internalHomOfEqualizer A M).obj N) ⟶ N := by
    let H := (internalHomOfEqualizer A M).obj N
    let V := (ihom M.X).obj N.X
    let i : H.X ⟶ V := internalHomι A M N
    let ev : M.X ⊗ V ⟶ N.X := (ihom.ev M.X).app N.X
    let e : M.X ⊗ H.X ⟶ N.X := MonoidalClosed.uncurry i
    let p : (A.X ⊗ M.X) ⊗ V ⟶ N.X :=
      (α_ A.X M.X V).hom ≫ (A.X ◁ ev) ≫ N.mod.smul
    let q : M.X ⊗ (A.X ⊗ V) ⟶ N.X :=
      (α_ M.X A.X V).inv ≫ ((β_ M.X A.X).hom ▷ V) ≫
        (α_ A.X M.X V).hom ≫ (A.X ◁ ev) ≫ N.mod.smul
    have hi : H.mod.smul ≫ i =
        (A.X ◁ i) ≫ MonoidalClosed.curry q := by
      let j : H ⟶ _ := equalizer.ι _ _
      have hj : H.mod.smul ≫ j.hom =
          (A.X ◁ j.hom) ≫ MonoidalClosed.curry q := by
        exact j.isModHom.smul_hom
      change H.mod.smul ≫ j.hom =
        (A.X ◁ j.hom) ≫ MonoidalClosed.curry q
      exact hj
    have he : e = (M.X ◁ i) ≫ ev := MonoidalClosed.uncurry_eq i
    have hact : (M.X ◁ MonoidalClosed.curry q) ≫ ev = q := by
      exact MonoidalClosed.whiskerLeft_curry_ihom_ev_app M.X N.X q
    have hpost : MonoidalClosed.uncurry
          (i ≫ internalHomPost A M N) =
        ((A.X ⊗ M.X) ◁ i) ≫ p := by
      rw [MonoidalClosed.uncurry_natural_left]
      dsimp only [internalHomPost, p]
      rw [MonoidalClosed.uncurry_curry]
    have hbalanceRev :
        (α_ M.X A.X H.X).hom ≫ (M.X ◁ H.mod.smul) ≫ e =
          (((β_ M.X A.X).hom ≫ M.mod.smul) ▷ H.X) ≫ e := by
      calc
        _ = (α_ M.X A.X H.X).hom ≫ (M.X ◁ H.mod.smul) ≫
            (M.X ◁ i) ≫ ev := by rw [he]
        _ = (α_ M.X A.X H.X).hom ≫
            (M.X ◁ (H.mod.smul ≫ i)) ≫ ev := by
              rw [whiskerLeft_comp]
              simp only [Category.assoc]
        _ = (α_ M.X A.X H.X).hom ≫
            (M.X ◁ ((A.X ◁ i) ≫ MonoidalClosed.curry q)) ≫ ev := by
              rw [hi]
        _ = (α_ M.X A.X H.X).hom ≫ (M.X ◁ (A.X ◁ i)) ≫
            (M.X ◁ MonoidalClosed.curry q) ≫ ev := by
              rw [whiskerLeft_comp]
              simp only [Category.assoc]
        _ = (α_ M.X A.X H.X).hom ≫
            (M.X ◁ (A.X ◁ i)) ≫ q := by rw [hact]
        _ = ((β_ M.X A.X).hom ▷ H.X) ≫
            ((A.X ⊗ M.X) ◁ i) ≫ p := by
              dsimp only [q, p]
              slice_lhs 2 3 => rw [associator_inv_naturality_right]
              simp only [Category.assoc, Iso.hom_inv_id_assoc]
              slice_lhs 1 2 => rw [whisker_exchange]
              simp only [Category.assoc]
        _ = ((β_ M.X A.X).hom ▷ H.X) ≫
            MonoidalClosed.uncurry (i ≫ internalHomPost A M N) := by
              rw [hpost]
        _ = ((β_ M.X A.X).hom ▷ H.X) ≫
            MonoidalClosed.uncurry (i ≫ internalHomPre A M N) := by
              rw [internalHom_condition A M N]
        _ = ((β_ M.X A.X).hom ▷ H.X) ≫
            (M.mod.smul ▷ H.X) ≫ e := by
              dsimp only [internalHomPre]
              rw [MonoidalClosed.uncurry_pre_app]
        _ = (((β_ M.X A.X).hom ≫ M.mod.smul) ▷ H.X) ≫ e := by
              rw [comp_whiskerRight]
              simp only [Category.assoc]
    have hbalance :
        (((β_ M.X A.X).hom ≫ M.mod.smul) ▷ H.X) ≫ e =
          (α_ M.X A.X H.X).hom ≫ (M.X ◁ H.mod.smul) ≫ e :=
      hbalanceRev.symm
    have hlinear :
        (α_ A.X M.X H.X).inv ≫ (M.mod.smul ▷ H.X) ≫ e =
          (A.X ◁ e) ≫ N.mod.smul := by
      calc
        _ = (α_ A.X M.X H.X).inv ≫
            MonoidalClosed.uncurry (i ≫ internalHomPre A M N) := by
              dsimp only [internalHomPre]
              rw [MonoidalClosed.uncurry_pre_app]
        _ = (α_ A.X M.X H.X).inv ≫
            MonoidalClosed.uncurry (i ≫ internalHomPost A M N) := by
              rw [internalHom_condition A M N]
        _ = (A.X ◁ e) ≫ N.mod.smul := by
              rw [hpost]
              dsimp only [p]
              rw [he]
              slice_lhs 2 3 => rw [associator_naturality_right]
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
              rw [← whiskerLeft_comp_assoc]
    exact relativeTensorDesc A M H N e hbalance hlinear
  have component_π (N : Mod C A.X) :
      relativeTensorπ A M ((internalHomOfEqualizer A M).obj N) ≫
          (component N).hom =
        MonoidalClosed.uncurry (internalHomι A M N) := by
    dsimp only [component]
    apply relativeTensorDesc_π
  have tensor_map_π {N N' : Mod C A.X} (g : N ⟶ N') :
      relativeTensorπ A M N ≫ (((relativeTensor A).obj M).map g).hom =
        (M.X ◁ g.hom) ≫ relativeTensorπ A M N' := by
    let _ : MonoidalCategory (Mod C A.X) := instMonoidalCategory A
    have hmap : relativeTensorMap A (𝟙 M) g =
        ((relativeTensor A).obj M).map g := by
      change (𝟙 M) ⊗ₘ g = M ◁ g
      exact id_tensorHom M g
    rw [← hmap, relativeTensorMap_π]
    simp only [Mod.id_hom', tensorHom_def, id_whiskerRight,
      Category.id_comp]
  exact
    { app := component
      naturality := by
        intro N N' g
        change ((relativeTensor A).obj M).map ((internalHomOfEqualizer A M).map g) ≫
            component N' = component N ≫ g
        apply relativeTensor_hom_ext A M ((internalHomOfEqualizer A M).obj N)
        simp only [Mod.comp_hom']
        slice_lhs 1 2 => rw [tensor_map_π]
        slice_lhs 2 3 => rw [component_π]
        slice_rhs 1 2 => rw [component_π]
        rw [← MonoidalClosed.uncurry_natural_left]
        rw [internalHomMap A M g]
        rw [MonoidalClosed.uncurry_natural_right] }

/-- Coevaluation into the module internal Hom from the balanced projection. -/
noncomputable def coevaluation (M : Mod C A.X) :
    𝟭 (Mod C A.X) ⟶ (relativeTensor A).obj M ⋙ internalHomOfEqualizer A M := by
  let _ : CreatesLimitsOfShape WalkingParallelPair
      (Mod.forget (D := C) A.X) := by
    let _ := Mod.forgetCreatesLimits.{0} A.X
    infer_instance
  let _ : HasLimitsOfShape WalkingParallelPair (Mod C A.X) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
      (Mod.forget (D := C) A.X)
  let componentData (N : Mod C A.X) :
      { f : N ⟶ (internalHomOfEqualizer A M).obj (((relativeTensor A).obj M).obj N) //
        f.hom ≫ internalHomι A M (((relativeTensor A).obj M).obj N) =
          MonoidalClosed.curry (relativeTensorπ A M N) } := by
    let T := ((relativeTensor A).obj M).obj N
    let W := (ihom M.X).obj T.X
    let π : M.X ⊗ N.X ⟶ T.X := relativeTensorπ A M N
    let k : N.X ⟶ W := MonoidalClosed.curry π
    let q : M.X ⊗ (A.X ⊗ W) ⟶ T.X :=
      (α_ M.X A.X W).inv ≫ ((β_ M.X A.X).hom ▷ W) ≫
        (α_ A.X M.X W).hom ≫
        (A.X ◁ (ihom.ev M.X).app T.X) ≫ T.mod.smul
    have hπlinear : (A.X ◁ π) ≫ T.mod.smul =
        (α_ A.X M.X N.X).inv ≫ (M.mod.smul ▷ N.X) ≫ π := by
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
    have hright : MonoidalClosed.uncurry
          ((A.X ◁ k) ≫ MonoidalClosed.curry q) =
        (α_ M.X A.X N.X).inv ≫ ((β_ M.X A.X).hom ▷ N.X) ≫
          MonoidalClosed.uncurry (k ≫ internalHomPost A M T) := by
      rw [MonoidalClosed.uncurry_natural_left,
        MonoidalClosed.uncurry_curry]
      rw [MonoidalClosed.uncurry_natural_left]
      dsimp only [internalHomPost]
      rw [MonoidalClosed.uncurry_curry]
      dsimp only [q]
      slice_lhs 1 2 => rw [associator_inv_naturality_right]
      slice_lhs 2 3 => rw [whisker_exchange]
      simp only [Category.assoc]
      rfl
    have hklinear : N.mod.smul ≫ k =
        (A.X ◁ k) ≫ MonoidalClosed.curry q := by
      apply MonoidalClosed.uncurry_injective
      rw [MonoidalClosed.uncurry_natural_left]
      dsimp only [k]
      rw [MonoidalClosed.uncurry_curry, hright]
      rw [← hfork]
      dsimp only [internalHomPre]
      rw [MonoidalClosed.uncurry_pre_app]
      dsimp only [k]
      rw [MonoidalClosed.uncurry_curry]
      slice_rhs 2 3 => rw [← comp_whiskerRight]
      change (M.X ◁ N.mod.smul) ≫ relativeTensorπ A M N =
        (α_ M.X A.X N.X).inv ≫ (braidedRightAction A M ▷ N.X) ≫
          relativeTensorπ A M N
      simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
        congrArg (fun f => (α_ M.X A.X N.X).inv ≫ f)
          (relativeTensorπ_balance A M N).symm
    let hlim := internalHomIsLimit A M T
    let ℓ : N.X ⟶ ((internalHomOfEqualizer A M).obj T).X :=
      Fork.IsLimit.lift hlim k hfork
    have hℓ : ℓ ≫ internalHomι A M T = k :=
      Fork.IsLimit.lift_ι' hlim k hfork
    have hi : ((internalHomOfEqualizer A M).obj T).mod.smul ≫
          internalHomι A M T =
        (A.X ◁ internalHomι A M T) ≫ MonoidalClosed.curry q := by
      let j : (internalHomOfEqualizer A M).obj T ⟶ _ := equalizer.ι _ _
      have hj : ((internalHomOfEqualizer A M).obj T).mod.smul ≫ j.hom =
          (A.X ◁ j.hom) ≫ MonoidalClosed.curry q := by
        exact j.isModHom.smul_hom
      change ((internalHomOfEqualizer A M).obj T).mod.smul ≫ j.hom =
        (A.X ◁ j.hom) ≫ MonoidalClosed.curry q
      exact hj
    have hℓlinear : N.mod.smul ≫ ℓ =
        (A.X ◁ ℓ) ≫ ((internalHomOfEqualizer A M).obj T).mod.smul := by
      let _ : Mono (internalHomι A M T) := Fork.IsLimit.mono hlim
      apply (cancel_mono (internalHomι A M T)).1
      calc
        (N.mod.smul ≫ ℓ) ≫ internalHomι A M T =
            N.mod.smul ≫ k := by
              rw [Category.assoc, hℓ]
        _ = (A.X ◁ k) ≫ MonoidalClosed.curry q := hklinear
        _ = (A.X ◁ (ℓ ≫ internalHomι A M T)) ≫
            MonoidalClosed.curry q := by rw [hℓ]
        _ = ((A.X ◁ ℓ) ≫ (A.X ◁ internalHomι A M T)) ≫
            MonoidalClosed.curry q := by
              rw [whiskerLeft_comp]
        _ = ((A.X ◁ ℓ) ≫ ((internalHomOfEqualizer A M).obj T).mod.smul) ≫
            internalHomι A M T := by
              simp only [Category.assoc]
              rw [hi]
    let f : N ⟶ (internalHomOfEqualizer A M).obj T := Mod.Hom.mk' ℓ hℓlinear
    refine ⟨f, ?_⟩
    exact hℓ
  let component (N : Mod C A.X) := (componentData N).1
  have component_ι (N : Mod C A.X) :
      (component N).hom ≫ internalHomι A M
          (((relativeTensor A).obj M).obj N) =
        MonoidalClosed.curry (relativeTensorπ A M N) :=
    (componentData N).2
  have tensor_map_π {N N' : Mod C A.X} (g : N ⟶ N') :
      relativeTensorπ A M N ≫ (((relativeTensor A).obj M).map g).hom =
        (M.X ◁ g.hom) ≫ relativeTensorπ A M N' := by
    let _ : MonoidalCategory (Mod C A.X) := instMonoidalCategory A
    have hmap : relativeTensorMap A (𝟙 M) g =
        ((relativeTensor A).obj M).map g := by
      change (𝟙 M) ⊗ₘ g = M ◁ g
      exact id_tensorHom M g
    rw [← hmap, relativeTensorMap_π]
    simp only [Mod.id_hom', tensorHom_def, id_whiskerRight,
      Category.id_comp]
  exact
    { app := component
      naturality := by
        intro N N' g
        change g ≫ component N' =
          component N ≫ (internalHomOfEqualizer A M).map
            (((relativeTensor A).obj M).map g)
        apply Mod.hom_ext
        apply Fork.IsLimit.hom_ext
          (internalHomIsLimit A M (((relativeTensor A).obj M).obj N'))
        simp only [Mod.comp_hom', Fork.ι_ofι]
        rw [Category.assoc, component_ι]
        rw [Category.assoc, internalHomMap, ← Category.assoc, component_ι]
        rw [← MonoidalClosed.curry_natural_left]
        rw [← MonoidalClosed.curry_natural_right]
        rw [tensor_map_π] }

/-- The balanced relative tensor is left adjoint to the module internal Hom. -/
noncomputable def relativeTensorInternalHomAdjunction (M : Mod C A.X) :
    (relativeTensor A).obj M ⊣ internalHomOfEqualizer A M := by
  let F := (relativeTensor A).obj M
  let G := internalHomOfEqualizer A M
  have tensor_map_π {X Y : Mod C A.X} (g : X ⟶ Y) :
      relativeTensorπ A M X ≫ (F.map g).hom =
        (M.X ◁ g.hom) ≫ relativeTensorπ A M Y := by
    let _ : MonoidalCategory (Mod C A.X) := instMonoidalCategory A
    have hmap : relativeTensorMap A (𝟙 M) g = F.map g := by
      change (𝟙 M) ⊗ₘ g = M ◁ g
      exact id_tensorHom M g
    rw [← hmap, relativeTensorMap_π]
    simp only [Mod.id_hom', tensorHom_def, id_whiskerRight,
      Category.id_comp]
  have evaluation_π (X : Mod C A.X) :
      relativeTensorπ A M (G.obj X) ≫ ((evaluation A M).app X).hom =
        MonoidalClosed.uncurry (internalHomι A M X) := by
    dsimp [G, evaluation]
    apply relativeTensorDesc_π
  have coevaluation_ι (X : Mod C A.X) :
      ((coevaluation A M).app X).hom ≫ internalHomι A M (F.obj X) =
        MonoidalClosed.curry (relativeTensorπ A M X) := by
    let T := F.obj X
    let π : M.X ⊗ X.X ⟶ T.X := relativeTensorπ A M X
    let k : X.X ⟶ (ihom M.X).obj T.X := MonoidalClosed.curry π
    have hπlinear : (A.X ◁ π) ≫ T.mod.smul =
        (α_ A.X M.X X.X).inv ≫ (M.mod.smul ▷ X.X) ≫ π := by
      dsimp only [T, F, π]
      exact Bimod.TensorBimod.whiskerLeft_π_actLeft
        (C := C) (R := A.toMon) (S := A.toMon) (T := A.toMon) _ _
    have hpre : MonoidalClosed.uncurry
          (k ≫ internalHomPre A M T) =
        (M.mod.smul ▷ X.X) ≫ π := by
      dsimp only [internalHomPre]
      rw [MonoidalClosed.uncurry_pre_app]
      dsimp only [k]
      rw [MonoidalClosed.uncurry_curry]
    have hpost : MonoidalClosed.uncurry
          (k ≫ internalHomPost A M T) =
        (α_ A.X M.X X.X).hom ≫ (A.X ◁ π) ≫ T.mod.smul := by
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
    have happ : ((coevaluation A M).app X).hom =
        Fork.IsLimit.lift (internalHomIsLimit A M T) k hfork := by
      unfold coevaluation
      rfl
    rw [happ]
    exact Fork.IsLimit.lift_ι' (internalHomIsLimit A M T) k hfork
  refine
    { unit := coevaluation A M
      counit := evaluation A M
      left_triangle_components := ?_
      right_triangle_components := ?_ }
  · intro N
    apply relativeTensor_hom_ext A M N
    change relativeTensorπ A M N ≫
          (F.map ((coevaluation A M).app N)).hom ≫
          ((evaluation A M).app (F.obj N)).hom =
        relativeTensorπ A M N ≫ (𝟙 (F.obj N) : F.obj N ⟶ F.obj N).hom
    simp only [Mod.id_hom']
    rw [← Category.assoc, tensor_map_π, Category.assoc]
    erw [evaluation_π (F.obj N)]
    rw [← MonoidalClosed.uncurry_natural_left, coevaluation_ι]
    rw [MonoidalClosed.uncurry_curry, Category.comp_id]
  · intro N
    apply Mod.hom_ext
    apply Fork.IsLimit.hom_ext (internalHomIsLimit A M N)
    simp only [Mod.comp_hom', Mod.id_hom', Fork.ι_ofι]
    erw [Category.assoc, internalHomMap]
    rw [← Category.assoc, coevaluation_ι]
    rw [← MonoidalClosed.curry_natural_right, evaluation_π]
    rw [MonoidalClosed.curry_uncurry, Category.id_comp]

/-- Explicit closed structure over the selected relative-tensor monoidal structure. -/
@[instance_reducible] noncomputable def instMonoidalClosed :
    @MonoidalClosed (Mod C A.X) _ (instMonoidalCategory A) := by
  letI : MonoidalCategory (Mod C A.X) := instMonoidalCategory A
  exact
    { closed := fun M =>
        { rightAdj := internalHomOfEqualizer A M
          adj := relativeTensorInternalHomAdjunction A M } }

end CategoryTheory.Mod
