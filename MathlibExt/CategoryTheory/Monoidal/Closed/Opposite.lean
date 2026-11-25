/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Opposite

/-!
# The chosen internal Hom on the monoidal opposite

For a braided monoidal closed category `C`, right tensoring by `X` is left
adjoint to `ihom X`. Transporting this adjunction gives a closed structure on
`Cᴹᵒᵖ`. There, the right adjoint to left tensoring by `X : Cᴹᵒᵖ` is
`unmopFunctor C ⋙ ihom (unmop X) ⋙ mopFunctor C`.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory MonoidalCategory MonoidalOpposite

namespace CategoryTheory.MonoidalOpposite

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C]

/-- In a braided monoidal closed category, right tensoring `Y ↦ Y ⊗ X` is left adjoint
to the chosen internal Hom `ihom X`. -/
def originalRightTensorAdjunction (X : C) : tensorRight X ⊣ ihom X :=
  (ihom.adjunction X).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight X)

/-- In a braided monoidal closed category, the right-tensor adjunction sends
`f : Y ⊗ X ⟶ Z` to `MonoidalClosed.curry ((β_ X Y).hom ≫ f)`. -/
theorem originalRightTensorAdjunction_homEquiv (X Y Z : C) (f : Y ⊗ X ⟶ Z) :
    (originalRightTensorAdjunction X).homEquiv Y Z f =
      MonoidalClosed.curry ((β_ X Y).hom ≫ f) := by
  rw [originalRightTensorAdjunction, Adjunction.homEquiv_ofNatIsoLeft_apply]
  rfl

/-- In a braided monoidal closed category, the counit at `Z` of the right-tensor
adjunction for `X` is `(β_ X ((ihom X).obj Z)).inv ≫ (ihom.ev X).app Z`. -/
theorem originalRightTensorAdjunction_counit (X Z : C) :
    (originalRightTensorAdjunction X).counit.app Z =
      (β_ X ((ihom X).obj Z)).inv ≫ (ihom.ev X).app Z := rfl

/-- If `C` is braided and monoidal closed, its monoidal opposite is closed with
right adjoint `unmopFunctor C ⋙ ihom (unmop X) ⋙ mopFunctor C` to left tensoring by `X`. -/
@[instance_reducible] def monoidalClosedOpposite : MonoidalClosed Cᴹᵒᵖ where
  closed X :=
    { rightAdj := unmopFunctor C ⋙ ihom (unmop X) ⋙ mopFunctor C
      adj := (((unmopEquiv C).toAdjunction.comp (originalRightTensorAdjunction (unmop X))).comp
        (mopEquiv C).toAdjunction).ofNatIsoLeft (tensorLeftIso X).symm }

/-- For `C` braided and monoidal closed, the chosen structure `monoidalClosedOpposite`
has `ihom X = unmopFunctor C ⋙ ihom (unmop X) ⋙ mopFunctor C` for `X : Cᴹᵒᵖ`. -/
theorem monoidalClosedOpposite_ihom (X : Cᴹᵒᵖ) :
    letI : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
    ihom X = unmopFunctor C ⋙ ihom (unmop X) ⋙ mopFunctor C := rfl

/-- For `C` braided and monoidal closed, the internal Hom from `mop X` to `mop Y`
in the chosen opposite structure unwraps to `(ihom X).obj Y`. -/
theorem monoidalClosedOpposite_ihom_obj (X Y : C) :
    letI : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
    unmop ((ihom (mop X)).obj (mop Y)) = (ihom X).obj Y := rfl

/-- For `C` braided and monoidal closed, applying the chosen opposite internal Hom
`ihom (mop X)` to `f.mop` and unwrapping gives `(ihom X).map f`. -/
theorem monoidalClosedOpposite_ihom_map (X : C) {Y Z : C} (f : Y ⟶ Z) :
    letI : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
    ((ihom (mop X)).map f.mop).unmop = (ihom X).map f := rfl

/-- For `C` braided and monoidal closed and `f : Y ⊗ X ⟶ Z`, the chosen opposite
left-tensor Hom bijection on `f.mop` unwraps to the right-tensor Hom bijection on `f`. -/
theorem monoidalClosedOpposite_homEquiv (X Y Z : C) (f : Y ⊗ X ⟶ Z) :
    letI : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
    (((ihom.adjunction (mop X)).homEquiv (mop Y) (mop Z)) f.mop).unmop =
      (originalRightTensorAdjunction X).homEquiv Y Z f := by
  let : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
  change ((((((unmopEquiv C).toAdjunction.comp (originalRightTensorAdjunction X)).comp
    (mopEquiv C).toAdjunction).ofNatIsoLeft (tensorLeftIso (mop X)).symm).homEquiv
      (mop Y) (mop Z)) f.mop).unmop = _
  erw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply, Adjunction.homEquiv_unit]
  simp only [mopEquiv, unmopEquiv, Equivalence.toAdjunction, Equivalence.unit,
    Equivalence.symm, tensorLeftIso]
  erw [CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.refl_inv, NatTrans.id_app]
  erw [CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.refl_inv, NatTrans.id_app]
  change 𝟙 Y ≫ ((originalRightTensorAdjunction X).unit.app Y ≫
    (ihom X).map (𝟙 (Y ⊗ X) ≫ 𝟙 (Y ⊗ X) ≫ f)) =
      (originalRightTensorAdjunction X).unit.app Y ≫ (ihom X).map f
  simp only [Category.id_comp]
  erw [Category.id_comp]

/-- In the chosen monoidal opposite of a braided monoidal closed category, the evaluation
at `mop Z` for `mop X` unwraps to the right-tensor counit at `Z` for `X`. -/
theorem monoidalClosedOpposite_counit (X Z : C) :
    letI : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
    ((ihom.ev (mop X)).app (mop Z)).unmop = (originalRightTensorAdjunction X).counit.app Z := by
  let : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
  let H := (ihom X).obj Z
  let opAdj := ihom.adjunction (mop X)
  let rAdj := originalRightTensorAdjunction X
  have hop : opAdj.homEquiv (mop H) (mop Z) (opAdj.counit.app (mop Z)) = 𝟙 (mop H) := by
    rw [← opAdj.homEquiv_symm_id (mop Z)]
    exact Equiv.apply_symm_apply _ _
  have hr : rAdj.homEquiv H Z (rAdj.counit.app Z) = 𝟙 H := by
    rw [← rAdj.homEquiv_symm_id Z]
    exact Equiv.apply_symm_apply _ _
  have h := monoidalClosedOpposite_homEquiv X H Z ((ihom.ev (mop X)).app (mop Z)).unmop
  change (opAdj.homEquiv (mop H) (mop Z) (opAdj.counit.app (mop Z))).unmop =
    rAdj.homEquiv H Z ((ihom.ev (mop X)).app (mop Z)).unmop at h
  rw [hop] at h
  change 𝟙 H = rAdj.homEquiv H Z ((ihom.ev (mop X)).app (mop Z)).unmop at h
  apply (rAdj.homEquiv H Z).injective
  exact h.symm.trans hr.symm

end CategoryTheory.MonoidalOpposite
