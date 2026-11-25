/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

module

public import MathlibExt.CategoryTheory.Monoidal.Mod.ColimitsFree
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# Internal-Hom equalizers for internal modules

This file equips ambient internal Homs with their canonical scalar action and
constructs the module internal Hom as the equalizer of the standard pre- and
post-action arrows. We work with left modules; commutativity and the ambient
braiding supply the scalar action on the equalizer.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory BraidedCategory MonObj
open scoped CategoryTheory.MonObj

universe v u

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]
variable [BraidedCategory C] [MonoidalClosed C]
/-- The actual associative action on the unchanged ambient internal-Hom carrier. -/
noncomputable abbrev internalHomAuxiliaryOfMonObj (R : C) [MonObj R] (U : C) (N : Mod C R) :
    Mod C R := by
  let H := (ihom U).obj N.X
  let q : U ⊗ (R ⊗ H) ⟶ N.X :=
    (α_ U R H).inv ≫ ((β_ U R).hom ▷ H) ≫
      (α_ R U H).hom ≫ (R ◁ (ihom.ev U).app N.X) ≫ N.mod.smul
  let act : R ⊗ H ⟶ H := MonoidalClosed.curry q
  refine { X := H, mod := { smul := act, one_smul := ?_, mul_smul := ?_ } }
  · apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
    dsimp only [act, q, H]
    change (U ◁ (η[R] ▷ H)) ≫ (α_ U R H).inv ≫
        ((β_ U R).hom ▷ H) ≫ (α_ R U H).hom ≫
        (R ◁ (ihom.ev U).app N.X) ≫ N.mod.smul =
      (U ◁ (λ_ H).hom) ≫ (ihom.ev U).app N.X
    have h : (U ◁ (η[R] ▷ H)) ≫ (α_ U R H).inv ≫
        ((β_ U R).hom ▷ H) ≫ (α_ R U H).hom ≫
        (R ◁ (ihom.ev U).app N.X) =
      (U ◁ (λ_ H).hom) ≫ (ihom.ev U).app N.X ≫
        (λ_ N.X).inv ≫ (η[R] ▷ N.X) := by
      slice_lhs 1 2 => rw [associator_inv_naturality_middle]
      slice_lhs 2 3 => rw [← comp_whiskerRight,
        braiding_naturality_right, comp_whiskerRight]
      slice_lhs 3 4 => rw [associator_naturality_left]
      slice_lhs 4 5 => rw [← whisker_exchange]
      have hb : (β_ U (𝟙_ C)).hom = (ρ_ U).hom ≫ (λ_ U).inv := by
        rw [← cancel_mono (λ_ U).hom, Category.assoc,
          Iso.inv_hom_id, Category.comp_id, braiding_leftUnitor]
      rw [hb]
      monoidal
    slice_lhs 1 5 => rw [h]
    simp
  · apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    change (U ◁ (μ[R] ▷ H)) ≫ q = MonoidalClosed.uncurry
      ((α_ R R H).hom ≫ (R ◁ act) ≫ act)
    rw [MonoidalClosed.uncurry_natural_left (α_ R R H).hom ((R ◁ act) ≫ act),
      MonoidalClosed.uncurry_natural_left (R ◁ act) act]
    dsimp only [act]
    rw [MonoidalClosed.uncurry_curry]
    let s := (U ◁ (α_ R R H).hom) ≫ (α_ U R (R ⊗ H)).inv ≫
      ((β_ U R).hom ▷ (R ⊗ H)) ≫ (α_ R U (R ⊗ H)).hom
    let w := s ≫ (R ◁ (U ◁ MonoidalClosed.curry q)) ≫
      (R ◁ (ihom.ev U).app N.X) ≫ N.mod.smul
    let nrm := (α_ U (R ⊗ R) H).inv ≫ ((β_ U (R ⊗ R)).hom ▷ H) ≫
      (α_ (R ⊗ R) U H).hom ≫ ((R ⊗ R) ◁ (ihom.ev U).app N.X) ≫
      (α_ R R N.X).hom ≫ (R ◁ N.mod.smul) ≫ N.mod.smul
    change (U ◁ (μ[R] ▷ H)) ≫ q =
      (U ◁ (α_ R R H).hom) ≫ (U ◁ (R ◁ MonoidalClosed.curry q)) ≫ q
    have hl : (U ◁ (μ[R] ▷ H)) ≫ q = nrm := by
      dsimp only [q, nrm]
      slice_rhs 5 7 => rw [← ModObj.mul_smul_self]
      slice_lhs 1 2 => rw [associator_inv_naturality_middle]
      slice_lhs 2 3 => rw [← comp_whiskerRight,
        braiding_naturality_right, comp_whiskerRight]
      slice_lhs 3 4 => rw [associator_naturality_left]
      slice_lhs 4 5 => rw [← whisker_exchange]
      monoidal
    have hr : (U ◁ (α_ R R H).hom) ≫
        (U ◁ (R ◁ MonoidalClosed.curry q)) ≫ q = w := by
      change (U ◁ (α_ R R H).hom) ≫ (U ◁ (R ◁ MonoidalClosed.curry q)) ≫
          (α_ U R H).inv ≫ ((β_ U R).hom ▷ H) ≫ (α_ R U H).hom ≫
          (R ◁ (ihom.ev U).app N.X) ≫ N.mod.smul =
        ((U ◁ (α_ R R H).hom) ≫ (α_ U R (R ⊗ H)).inv ≫
          ((β_ U R).hom ▷ (R ⊗ H)) ≫ (α_ R U (R ⊗ H)).hom) ≫
          (R ◁ (U ◁ MonoidalClosed.curry q)) ≫
          (R ◁ (ihom.ev U).app N.X) ≫ N.mod.smul
      dsimp only [H]
      slice_lhs 2 3 => rw [associator_inv_naturality_right]
      slice_lhs 3 4 => rw [whisker_exchange]
      slice_lhs 4 5 => rw [associator_naturality_right]
      monoidal
    have hw : w = nrm := by
      dsimp only [w, s]
      slice_lhs 5 6 => rw [← whiskerLeft_comp, MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
      dsimp only [q, nrm]
      rw [braiding_tensor_right_hom]
      monoidal
    exact hl.trans (hr.trans hw).symm

/-- The general auxiliary module retains its original ambient internal-Hom carrier. -/
theorem internalHomAuxiliaryOfMonObj_obj (R : C) [MonObj R] (U : C) (N : Mod C R) :
    (internalHomAuxiliaryOfMonObj R U N).X = (ihom U).obj N.X := rfl

/-- Every target module morphism induces the original auxiliary internal-Hom map. -/
noncomputable abbrev internalHomAuxiliaryOfMonObjMap (R : C) [MonObj R]
    {N N' : Mod C R} (g : N ⟶ N') (X : C) :
    internalHomAuxiliaryOfMonObj R X N ⟶ internalHomAuxiliaryOfMonObj R X N' :=
  Mod.Hom.mk' ((ihom X).map g.hom) (by
    let H := (ihom X).obj N.X
    let H' := (ihom X).obj N'.X
    let u : X ⊗ (R ⊗ H) ⟶ N.X := (α_ X R H).inv ≫
      ((β_ X R).hom ▷ H) ≫ (α_ R X H).hom ≫
      (R ◁ (ihom.ev X).app N.X) ≫ N.mod.smul
    let u' : X ⊗ (R ⊗ H') ⟶ N'.X := (α_ X R H').inv ≫
      ((β_ X R).hom ▷ H') ≫ (α_ R X H').hom ≫
      (R ◁ (ihom.ev X).app N'.X) ≫ N'.mod.smul
    change MonoidalClosed.curry u ≫ (ihom X).map g.hom =
      (R ◁ (ihom X).map g.hom) ≫ MonoidalClosed.curry u'
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_right,
      MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry]
    change u ≫ g.hom = (X ◁ (R ◁ (ihom X).map g.hom)) ≫ u'
    have h₁ := associator_inv_naturality_right X R ((ihom X).map g.hom)
    have h₂ := whisker_exchange (β_ X R).hom ((ihom X).map g.hom)
    have h₃ := associator_naturality_right R X ((ihom X).map g.hom)
    slice_rhs 1 2 => rw [h₁]
    slice_rhs 2 3 => rw [h₂]
    slice_rhs 3 4 => rw [h₃]
    slice_rhs 4 5 => rw [← whiskerLeft_comp,
      ihom.ev_naturality, whiskerLeft_comp]
    have hg : (R ◁ g.hom) ≫ N'.mod.smul = N.mod.smul ≫ g.hom :=
      (IsModHom.smul_hom (A := R) (f := g.hom)).symm
    simp only [Category.assoc]
    rw [hg]
    dsimp only [u, u', H, H']
    monoidal)

variable (A : CommMon C)

/-- The commutative API uses the general original monoid auxiliary action. -/
noncomputable abbrev internalHomAuxiliary (X : C) (N : Mod C A.X) : Mod C A.X :=
  internalHomAuxiliaryOfMonObj A.X X N

/-- The original auxiliary module has the unchanged ambient internal-Hom carrier. -/
theorem internalHomAuxiliary_obj (X : C) (N : Mod C A.X) :
    (internalHomAuxiliary A X N).X = (ihom X).obj N.X := rfl

/-- The original auxiliary action is the actual coefficient shuffle, evaluation
and target module action. -/
theorem internalHomAuxiliary_smul (X : C) (N : Mod C A.X) :
    (internalHomAuxiliary A X N).mod.smul = MonoidalClosed.curry
      ((α_ X A.X ((ihom X).obj N.X)).inv ≫
        ((β_ X A.X).hom ▷ (ihom X).obj N.X) ≫
        (α_ A.X X ((ihom X).obj N.X)).hom ≫
        (A.X ◁ (ihom.ev X).app N.X) ≫ N.mod.smul) := rfl

/-- Precomposition by the source module action in the equalizer pair. -/
noncomputable def internalHomPre (M N : Mod C A.X) :
    (ihom M.X).obj N.X ⟶ (ihom (A.X ⊗ M.X)).obj N.X :=
  (MonoidalClosed.pre M.mod.smul).app N.X

/-- Postcomposition by the target scalar action in the equalizer pair. -/
noncomputable def internalHomPost (M N : Mod C A.X) :
    (ihom M.X).obj N.X ⟶ (ihom (A.X ⊗ M.X)).obj N.X :=
  MonoidalClosed.curry
    ((α_ A.X M.X ((ihom M.X).obj N.X)).hom ≫
      (A.X ◁ (ihom.ev M.X).app N.X) ≫ N.mod.smul)

/-- Every entire original source arrow is linear for the original auxiliary
internal-Hom action. This exposes the pre-linearity used by the equalizer. -/
theorem internalHomAuxiliary_pre_linear (X Y : C) (f : Y ⟶ X) (N : Mod C A.X) :
    (internalHomAuxiliary A X N).mod.smul ≫ (MonoidalClosed.pre f).app N.X =
      (A.X ◁ (MonoidalClosed.pre f).app N.X) ≫
        (internalHomAuxiliary A Y N).mod.smul := by
  let HX := (ihom X).obj N.X
  let HY := (ihom Y).obj N.X
  let uX : X ⊗ (A.X ⊗ HX) ⟶ N.X := (α_ X A.X HX).inv ≫
    ((β_ X A.X).hom ▷ HX) ≫ (α_ A.X X HX).hom ≫
    (A.X ◁ (ihom.ev X).app N.X) ≫ N.mod.smul
  let uY : Y ⊗ (A.X ⊗ HY) ⟶ N.X := (α_ Y A.X HY).inv ≫
    ((β_ Y A.X).hom ▷ HY) ≫ (α_ A.X Y HY).hom ≫
    (A.X ◁ (ihom.ev Y).app N.X) ≫ N.mod.smul
  change MonoidalClosed.curry uX ≫ (MonoidalClosed.pre f).app N.X =
    (A.X ◁ (MonoidalClosed.pre f).app N.X) ≫
      MonoidalClosed.curry uY
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
  change (f ▷ (A.X ⊗ HX)) ≫ uX =
    (Y ◁ (A.X ◁ (MonoidalClosed.pre f).app N.X)) ≫ uY
  slice_rhs 1 2 => rw [associator_inv_naturality_right]
  slice_rhs 2 3 => rw [whisker_exchange]
  slice_rhs 3 4 => rw [associator_naturality_right]
  slice_rhs 4 5 => rw [← whiskerLeft_comp,
    MonoidalClosed.id_tensor_pre_app_comp_ev, whiskerLeft_comp]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight,
    BraidedCategory.braiding_naturality_left, comp_whiskerRight]
  slice_lhs 3 4 => rw [associator_naturality_middle]
  dsimp only [uX, uY, HX, HY]
  monoidal

/-- The module map induced by precomposition with the source module action. -/
noncomputable def internalHomPreLinear (M N : Mod C A.X) :
    internalHomAuxiliary A M.X N ⟶ internalHomAuxiliary A (A.X ⊗ M.X) N :=
  Mod.Hom.mk' (internalHomPre A M N)
    (internalHomAuxiliary_pre_linear A M.X (A.X ⊗ M.X) M.mod.smul N)

/-- The module map induced by postcomposition with the target module action. -/
noncomputable def internalHomPostLinear (M N : Mod C A.X) :
    internalHomAuxiliary A M.X N ⟶ internalHomAuxiliary A (A.X ⊗ M.X) N :=
  Mod.Hom.mk' (internalHomPost A M N) (by
    let H := (ihom M.X).obj N.X
    let K := (ihom (A.X ⊗ M.X)).obj N.X
    let uM : M.X ⊗ (A.X ⊗ H) ⟶ N.X := (α_ M.X A.X H).inv ≫
      ((β_ M.X A.X).hom ▷ H) ≫ (α_ A.X M.X H).hom ≫
      (A.X ◁ (ihom.ev M.X).app N.X) ≫ N.mod.smul
    let p : (A.X ⊗ M.X) ⊗ H ⟶ N.X := (α_ A.X M.X H).hom ≫
      (A.X ◁ (ihom.ev M.X).app N.X) ≫ N.mod.smul
    let uAM : (A.X ⊗ M.X) ⊗ (A.X ⊗ K) ⟶ N.X :=
      (α_ (A.X ⊗ M.X) A.X K).inv ≫
      ((β_ (A.X ⊗ M.X) A.X).hom ▷ K) ≫
      (α_ A.X (A.X ⊗ M.X) K).hom ≫
      (A.X ◁ (ihom.ev (A.X ⊗ M.X)).app N.X) ≫ N.mod.smul
    change MonoidalClosed.curry uM ≫ internalHomPost A M N =
      (A.X ◁ internalHomPost A M N) ≫ MonoidalClosed.curry uAM
    apply MonoidalClosed.uncurry_injective
    dsimp only [internalHomPost]
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
      MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry]
    change ((A.X ⊗ M.X) ◁ MonoidalClosed.curry uM) ≫ p =
      ((A.X ⊗ M.X) ◁ (A.X ◁ MonoidalClosed.curry p)) ≫ uAM
    let t := (α_ A.X M.X (A.X ⊗ H)).hom ≫
      (A.X ◁ (α_ M.X A.X H).inv) ≫
      (A.X ◁ ((β_ M.X A.X).hom ▷ H)) ≫
      (A.X ◁ (α_ A.X M.X H).hom) ≫
      (α_ A.X A.X (M.X ⊗ H)).inv
    let v := t ≫ ((A.X ⊗ A.X) ◁ (ihom.ev M.X).app N.X) ≫
      (α_ A.X A.X N.X).hom ≫ (A.X ◁ N.mod.smul) ≫ N.mod.smul
    let vs := t ≫ ((β_ A.X A.X).hom ▷ (M.X ⊗ H)) ≫
      ((A.X ⊗ A.X) ◁ (ihom.ev M.X).app N.X) ≫
      (α_ A.X A.X N.X).hom ≫ (A.X ◁ N.mod.smul) ≫ N.mod.smul
    slice_lhs 1 2 => rw [associator_naturality_right]
    slice_lhs 2 3 => rw [← whiskerLeft_comp,
      MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    have h₁ := associator_inv_naturality_right (A.X ⊗ M.X) A.X
      (MonoidalClosed.curry p)
    have h₂ := whisker_exchange (β_ (A.X ⊗ M.X) A.X).hom
      (MonoidalClosed.curry p)
    have h₃ := associator_naturality_right A.X (A.X ⊗ M.X)
      (MonoidalClosed.curry p)
    slice_rhs 1 2 => rw [h₁]
    slice_rhs 2 3 => rw [h₂]
    slice_rhs 3 4 => rw [h₃]
    slice_rhs 4 5 => rw [← whiskerLeft_comp,
      MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
    change (α_ A.X M.X (A.X ⊗ H)).hom ≫ (A.X ◁ uM) ≫ N.mod.smul =
      (α_ (A.X ⊗ M.X) A.X H).inv ≫
      ((β_ (A.X ⊗ M.X) A.X).hom ▷ H) ≫
      (α_ A.X (A.X ⊗ M.X) H).hom ≫ (A.X ◁ p) ≫ N.mod.smul
    have hl : (α_ A.X M.X (A.X ⊗ H)).hom ≫
        (A.X ◁ uM) ≫ N.mod.smul = v := by
      dsimp only [uM, v, t]
      monoidal
    have hr : (α_ (A.X ⊗ M.X) A.X H).inv ≫
        ((β_ (A.X ⊗ M.X) A.X).hom ▷ H) ≫
        (α_ A.X (A.X ⊗ M.X) H).hom ≫ (A.X ◁ p) ≫ N.mod.smul = vs := by
      dsimp only [p, vs, t]
      rw [BraidedCategory.braiding_tensor_left_hom]
      monoidal
    have hcomm : (β_ A.X A.X).hom ▷ N.X ≫
        (α_ A.X A.X N.X).hom ≫ (A.X ◁ N.mod.smul) ≫ N.mod.smul =
        (α_ A.X A.X N.X).hom ≫ (A.X ◁ N.mod.smul) ≫ N.mod.smul := by
      rw [← ModObj.mul_smul_self]
      slice_lhs 1 2 => rw [← comp_whiskerRight, IsCommMonObj.mul_comm]
    have hsv : vs = v := by
      dsimp only [vs, v]
      have hexchange : (β_ A.X A.X).hom ▷ (M.X ⊗ H) ≫
          ((A.X ⊗ A.X) ◁ (ihom.ev M.X).app N.X) =
        ((A.X ⊗ A.X) ◁ (ihom.ev M.X).app N.X) ≫
          ((β_ A.X A.X).hom ▷ N.X) :=
        (whisker_exchange (β_ A.X A.X).hom
          ((ihom.ev M.X).app N.X)).symm
      rw [← Category.assoc ((β_ A.X A.X).hom ▷ (M.X ⊗ H))
        ((A.X ⊗ A.X) ◁ (ihom.ev M.X).app N.X)]
      rw [hexchange]
      simp only [Category.assoc]
      rw [hcomm]
    exact hl.trans (hr.trans hsv).symm)

section Equalizer

variable [HasEqualizers C]

/-- The module forgetful functor creates equalizers using its existing
limits-creation instance for the original ambient carrier and maps. -/
noncomputable local instance forgetCreatesEqualizers :
    CreatesLimitsOfShape WalkingParallelPair (Mod.forget (D := C) A.X) := by
  let _ := Mod.forgetCreatesLimits.{0} A.X
  infer_instance

noncomputable local instance :
    HasLimitsOfShape WalkingParallelPair (Mod C A.X) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (Mod.forget (D := C) A.X)

/-- The internal Hom module map induced by a target module morphism. -/
noncomputable abbrev internalHomAuxiliaryMap {N N' : Mod C A.X}
    (g : N ⟶ N') (X : C) : internalHomAuxiliary A X N ⟶ internalHomAuxiliary A X N' :=
  internalHomAuxiliaryOfMonObjMap A.X g X

/-- The map of internal Hom equalizers induced by a target module morphism. -/
noncomputable def internalHomEqualizerMap (M : Mod C A.X)
    {N N' : Mod C A.X} (g : N ⟶ N') :
    equalizer (internalHomPreLinear A M N) (internalHomPostLinear A M N) ⟶
      equalizer (internalHomPreLinear A M N') (internalHomPostLinear A M N') := by
  have preSquare : internalHomPreLinear A M N ≫
        internalHomAuxiliaryMap A g (A.X ⊗ M.X) =
      internalHomAuxiliaryMap A g M.X ≫ internalHomPreLinear A M N' := by
    apply Mod.hom_ext
    exact MonoidalClosed.pre_comm_ihom_map M.mod.smul g.hom
  have postSquare : internalHomPostLinear A M N ≫
        internalHomAuxiliaryMap A g (A.X ⊗ M.X) =
      internalHomAuxiliaryMap A g M.X ≫ internalHomPostLinear A M N' := by
    apply Mod.hom_ext
    change internalHomPost A M N ≫ (ihom (A.X ⊗ M.X)).map g.hom =
      (ihom M.X).map g.hom ≫ internalHomPost A M N'
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_natural_right,
      MonoidalClosed.uncurry_natural_left]
    dsimp only [internalHomPost]
    rw [MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_curry]
    slice_rhs 1 2 => rw [associator_naturality_right]
    slice_rhs 2 3 => rw [← whiskerLeft_comp,
      ihom.ev_naturality, whiskerLeft_comp]
    have hg : (A.X ◁ g.hom) ≫ N'.mod.smul = N.mod.smul ≫ g.hom :=
      (IsModHom.smul_hom (A := A.X) (f := g.hom)).symm
    simp only [Category.assoc]
    rw [hg]
  refine equalizer.lift
    (equalizer.ι (internalHomPreLinear A M N) (internalHomPostLinear A M N) ≫
      internalHomAuxiliaryMap A g M.X) ?_
  slice_lhs 2 3 => rw [← preSquare]
  slice_lhs 1 2 => rw [equalizer.condition]
  slice_lhs 2 3 => rw [postSquare]
  simp only [Category.assoc]

/-- The module internal Hom, covariant in the target module. -/
noncomputable def internalHomOfEqualizer (M : Mod C A.X) : Mod C A.X ⥤ Mod C A.X where
  obj N := equalizer (internalHomPreLinear A M N) (internalHomPostLinear A M N)
  map g := internalHomEqualizerMap A M g
  map_id N := by
    apply equalizer.hom_ext
    dsimp [internalHomEqualizerMap]
    rw [equalizer.lift_ι]
    rw [Category.id_comp]
    convert Category.comp_id (equalizer.ι
      (internalHomPreLinear A M N) (internalHomPostLinear A M N)) using 1
    apply Mod.hom_ext
    simp only [Mod.comp_hom', Mod.id_hom']
    change (equalizer.ι (internalHomPreLinear A M N)
        (internalHomPostLinear A M N)).hom ≫
          (ihom M.X).map (𝟙 N.X) =
      (equalizer.ι (internalHomPreLinear A M N)
        (internalHomPostLinear A M N)).hom ≫ 𝟙 _
    rw [Functor.map_id]
  map_comp f g := by
    apply equalizer.hom_ext
    dsimp [internalHomEqualizerMap]
    rw [equalizer.lift_ι]
    rw [Category.assoc, equalizer.lift_ι]
    rw [← Category.assoc, equalizer.lift_ι]
    apply Mod.hom_ext
    simp only [Mod.comp_hom']
    change (equalizer.ι (internalHomPreLinear A M _)
        (internalHomPostLinear A M _)).hom ≫
          (ihom M.X).map (f.hom ≫ g.hom) =
      ((equalizer.ι (internalHomPreLinear A M _)
          (internalHomPostLinear A M _)).hom ≫
        (ihom M.X).map f.hom) ≫ (ihom M.X).map g.hom
    rw [Functor.map_comp, Category.assoc]

/-- Inclusion of the module internal Hom into the ambient internal Hom. -/
noncomputable def internalHomι (M N : Mod C A.X) :
    ((internalHomOfEqualizer A M).obj N).X ⟶ (ihom M.X).obj N.X :=
  (equalizer.ι (internalHomPreLinear A M N)
    (internalHomPostLinear A M N)).hom

set_option linter.unusedSectionVars false in
/-- The inclusion equalizes the two standard action arrows. -/
theorem internalHom_condition (M N : Mod C A.X) :
    internalHomι A M N ≫ internalHomPre A M N =
      internalHomι A M N ≫ internalHomPost A M N := by
  have h := congrArg Mod.Hom.hom (equalizer.condition
    (internalHomPreLinear A M N) (internalHomPostLinear A M N))
  exact h

/-- The ambient action fork is a limiting fork. -/
noncomputable def internalHomIsLimit (M N : Mod C A.X) :
    IsLimit (Fork.ofι (internalHomι A M N)
      (internalHom_condition A M N)) := by
  have h := isLimitForkMapOfIsLimit (G := Mod.forget (D := C) A.X)
    (equalizer.condition (internalHomPreLinear A M N)
      (internalHomPostLinear A M N))
    (equalizerIsEqualizer (internalHomPreLinear A M N)
      (internalHomPostLinear A M N))
  change IsLimit (Fork.ofι
    ((Mod.forget (D := C) A.X).map (equalizer.ι
      (internalHomPreLinear A M N) (internalHomPostLinear A M N))) _)
  exact h

/-- Characteristic equation for postcomposition on the internal Hom. -/
theorem internalHomMap (M : Mod C A.X) {N N' : Mod C A.X} (g : N ⟶ N') :
    ((internalHomOfEqualizer A M).map g).hom ≫ internalHomι A M N' =
      internalHomι A M N ≫ (ihom M.X).map g.hom := by
  change (internalHomEqualizerMap A M g ≫
      equalizer.ι (internalHomPreLinear A M N')
        (internalHomPostLinear A M N')).hom =
    (equalizer.ι (internalHomPreLinear A M N)
      (internalHomPostLinear A M N) ≫ internalHomAuxiliaryMap A g M.X).hom
  unfold internalHomEqualizerMap
  rw [equalizer.lift_ι]

/-- The original internal-Hom equalizer inclusion is linear into its actual
unchanged auxiliary module. -/
@[reassoc]
theorem internalHomι_smul (M N : Mod C A.X) :
    ((internalHomOfEqualizer A M).obj N).mod.smul ≫ internalHomι A M N =
      (A.X ◁ internalHomι A M N) ≫ (internalHomAuxiliary A M.X N).mod.smul := by
  let j : (internalHomOfEqualizer A M).obj N ⟶ internalHomAuxiliary A M.X N := equalizer.ι _ _
  exact j.isModHom.smul_hom

end Equalizer

end CategoryTheory.Mod
