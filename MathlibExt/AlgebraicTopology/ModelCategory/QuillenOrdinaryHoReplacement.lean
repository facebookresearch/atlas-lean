/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenOrdinaryHoHom

/-!
# Complete ordinary Ho functions with actual cofibrant replacements

An actual weak replacement of an arbitrary coefficient gives an isomorphism
in the original canonical localization. Its two precomposition functions
transport the checked Quillen ordinary Ho Hom equivalence. Both provided
replacement maps remain explicit in all coefficient squares and changes
of replacement. The original model's actual resolution constructs the
specialization for every coefficient without a replacement premise.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u₁ u₂ v₁ v₂

open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.QuillenOrdinaryHoReplacement

variable {C : Type u₁} [Category.{v₁} C] [ModelCategory C]
  {D : Type u₂} [Category.{v₂} D] [ModelCategory D]

local notation "HC" => CategoryTheory.MorphismProperty.Q (weakEquivalences C)
local notation "HD" => CategoryTheory.MorphismProperty.Q (weakEquivalences D)

/-- The actual weak replacement is an isomorphism in the original canonical ordinary Ho. -/
def replacementHoIso {Xc X : C} (pX : Xc ⟶ X) [WeakEquivalence pX] :
    (HC).obj Xc ≅ (HC).obj X := by
  let : IsIso ((HC).map pX) := Localization.inverts (HC) (weakEquivalences C)
    pX ((HomotopicalAlgebra.weakEquivalence_iff pX).1 inferInstance)
  exact asIso ((HC).map pX)

/-- The complete original precomposition and inverse functions keep the same replacement map. -/
def replacementPrecompEquiv {Xc X : C} (pX : Xc ⟶ X) [WeakEquivalence pX] (T : C) :
    ((HC).obj X ⟶ (HC).obj T) ≃ ((HC).obj Xc ⟶ (HC).obj T) where
  toFun f := (replacementHoIso pX).hom ≫ f
  invFun f := (replacementHoIso pX).inv ≫ f
  left_inv f := by
    change (replacementHoIso pX).inv ≫ ((replacementHoIso pX).hom ≫ f) = f
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  right_inv f := by
    change (replacementHoIso pX).hom ≫ ((replacementHoIso pX).inv ≫ f) = f
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The whole forward precomposition function is the actual original mapped replacement. -/
theorem replacementPrecompEquiv_apply {Xc X : C} (pX : Xc ⟶ X) [WeakEquivalence pX]
    (T : C) (f : (HC).obj X ⟶ (HC).obj T) :
    replacementPrecompEquiv pX T f = (HC).map pX ≫ f := rfl

/-- The whole inverse precomposition function uses the same actual mapped replacement. -/
theorem replacementPrecompEquiv_symm_apply {Xc X : C} (pX : Xc ⟶ X) [WeakEquivalence pX]
    (T : C) (f : (HC).obj Xc ⟶ (HC).obj T) :
    (replacementPrecompEquiv pX T).symm f = (replacementHoIso pX).inv ≫ f := rfl

/-- The whole forward precomposition function is natural in every actual target map. -/
theorem replacementPrecompEquiv_target {Xc X T T' : C} (pX : Xc ⟶ X) [WeakEquivalence pX]
    (f : (HC).obj X ⟶ (HC).obj T) (g : T ⟶ T') :
    replacementPrecompEquiv pX T' (f ≫ (HC).map g) =
      replacementPrecompEquiv pX T f ≫ (HC).map g := by
  change (replacementHoIso pX).hom ≫ (f ≫ (HC).map g) =
    ((replacementHoIso pX).hom ≫ f) ≫ (HC).map g
  exact (Category.assoc _ _ _).symm

/-- The whole inverse precomposition function is natural in every actual target map. -/
theorem replacementPrecompEquiv_symm_target {Xc X T T' : C}
    (pX : Xc ⟶ X) [WeakEquivalence pX]
    (f : (HC).obj Xc ⟶ (HC).obj T) (g : T ⟶ T') :
    (replacementPrecompEquiv pX T').symm (f ≫ (HC).map g) =
      (replacementPrecompEquiv pX T).symm f ≫ (HC).map g := by
  change (replacementHoIso pX).inv ≫ (f ≫ (HC).map g) =
    ((replacementHoIso pX).inv ≫ f) ≫ (HC).map g
  exact (Category.assoc _ _ _).symm

/-- The full precomposition square keeps both original replacements and both coefficient maps. -/
theorem replacementPrecompEquiv_coefficient {Xc X Xc' X' T : C}
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X') [WeakEquivalence pX']
    (a : X' ⟶ X) (ac : Xc' ⟶ Xc) (h : ac ≫ pX = pX' ≫ a)
    (f : (HC).obj X ⟶ (HC).obj T) :
    replacementPrecompEquiv pX' T ((HC).map a ≫ f) =
      (HC).map ac ≫ replacementPrecompEquiv pX T f := by
  change (HC).map pX' ≫ ((HC).map a ≫ f) = (HC).map ac ≫ ((HC).map pX ≫ f)
  rw [← Category.assoc, ← (HC).map_comp, ← h, (HC).map_comp, Category.assoc]

variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [Adjunction.IsQuillenAdjunction adj]

/-- The actual original Hom equivalence with any given weak cofibrant replacement. -/
def homEquiv {Xc X : C} [IsCofibrant Xc] (pX : Xc ⟶ X) [WeakEquivalence pX]
    (Y : D) [IsFibrant Y] :
    ((HD).obj (L.obj Xc) ⟶ (HD).obj Y) ≃ ((HC).obj X ⟶ (HC).obj (R.obj Y)) :=
  (QuillenOrdinaryHoHom.homEquiv adj Xc Y).trans
    (replacementPrecompEquiv pX (R.obj Y)).symm

/-- The entire forward Hom function retains the actual inverse replacement and original adjunct. -/
theorem homEquiv_apply {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] (Y : D) [IsFibrant Y]
    (f : (HD).obj (L.obj Xc) ⟶ (HD).obj Y) :
    homEquiv adj pX Y f = (replacementHoIso pX).inv ≫
      QuillenOrdinaryHoHom.homEquiv adj Xc Y f := rfl

/-- The entire inverse Hom function retains the same original replacement before inverse adjunct. -/
theorem homEquiv_symm_apply {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] (Y : D) [IsFibrant Y]
    (f : (HC).obj X ⟶ (HC).obj (R.obj Y)) :
    (homEquiv adj pX Y).symm f =
      (QuillenOrdinaryHoHom.homEquiv adj Xc Y).symm ((HC).map pX ≫ f) := rfl

/-- Actual replacement precomposition recovers the entire original cofibrant adjunct function. -/
theorem replacementPrecomp_homEquiv {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] (Y : D) [IsFibrant Y]
    (f : (HD).obj (L.obj Xc) ⟶ (HD).obj Y) :
    replacementPrecompEquiv pX (R.obj Y) (homEquiv adj pX Y f) =
      QuillenOrdinaryHoHom.homEquiv adj Xc Y f :=
  (replacementPrecompEquiv pX (R.obj Y)).apply_symm_apply _

/-- Every represented target arrow uses the same actual original adjunct and inverse replacement. -/
theorem homEquiv_map {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] (Y : D) [IsFibrant Y] (f : L.obj Xc ⟶ Y) :
    homEquiv adj pX Y ((HD).map f) =
      (replacementHoIso pX).inv ≫ (HC).map (adj.homEquiv Xc Y f) := by
  rw [homEquiv_apply, QuillenOrdinaryHoHom.homEquiv_map]

/-- The whole forward Hom function is natural in every actual fibrant target map. -/
theorem homEquiv_target {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] {Y Y' : D} [IsFibrant Y] [IsFibrant Y']
    (f : (HD).obj (L.obj Xc) ⟶ (HD).obj Y) (g : Y ⟶ Y') :
    homEquiv adj pX Y' (f ≫ (HD).map g) =
      homEquiv adj pX Y f ≫ (HC).map (R.map g) := by
  rw [homEquiv_apply, homEquiv_apply,
    QuillenOrdinaryHoHom.homEquiv_naturality_right, Category.assoc]

/-- The whole inverse Hom function is natural in every actual fibrant target map. -/
theorem homEquiv_symm_target {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] {Y Y' : D} [IsFibrant Y] [IsFibrant Y']
    (f : (HC).obj X ⟶ (HC).obj (R.obj Y)) (g : Y ⟶ Y') :
    (homEquiv adj pX Y').symm (f ≫ (HC).map (R.map g)) =
      (homEquiv adj pX Y).symm f ≫ (HD).map g := by
  apply (homEquiv adj pX Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_target, Equiv.apply_symm_apply]

/-- Every entire original replacement square gives the full coefficient naturality law. -/
theorem homEquiv_coefficient {Xc X Xc' X' : C} [IsCofibrant Xc] [IsCofibrant Xc']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X') [WeakEquivalence pX']
    (Y : D) [IsFibrant Y] (a : X' ⟶ X) (ac : Xc' ⟶ Xc)
    (h : ac ≫ pX = pX' ≫ a) (f : (HD).obj (L.obj Xc) ⟶ (HD).obj Y) :
    homEquiv adj pX' Y ((HD).map (L.map ac) ≫ f) =
      (HC).map a ≫ homEquiv adj pX Y f := by
  apply (replacementPrecompEquiv pX' (R.obj Y)).injective
  rw [replacementPrecomp_homEquiv, replacementPrecompEquiv_coefficient pX pX' a ac h,
    replacementPrecomp_homEquiv, QuillenOrdinaryHoHom.homEquiv_naturality_left]

/-- The inverse function retains the same full replacement square and both coefficient maps. -/
theorem homEquiv_symm_coefficient {Xc X Xc' X' : C}
    [IsCofibrant Xc] [IsCofibrant Xc']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X') [WeakEquivalence pX']
    (Y : D) [IsFibrant Y] (a : X' ⟶ X) (ac : Xc' ⟶ Xc)
    (h : ac ≫ pX = pX' ≫ a) (f : (HC).obj X ⟶ (HC).obj (R.obj Y)) :
    (homEquiv adj pX' Y).symm ((HC).map a ≫ f) =
      (HD).map (L.map ac) ≫ (homEquiv adj pX Y).symm f := by
  apply (homEquiv adj pX' Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_coefficient adj pX pX' Y a ac h,
    Equiv.apply_symm_apply]

/-- Both complete functions compare any two actual given weak cofibrant replacements. -/
def changeReplacement {Xc Xc' X : C} [IsCofibrant Xc] [IsCofibrant Xc']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X) [WeakEquivalence pX']
    (Y : D) [IsFibrant Y] :
    ((HD).obj (L.obj Xc) ⟶ (HD).obj Y) ≃ ((HD).obj (L.obj Xc') ⟶ (HD).obj Y) :=
  (homEquiv adj pX Y).trans (homEquiv adj pX' Y).symm

/-- The entire change-of-replacement function uses both original provided Hom functions. -/
theorem changeReplacement_apply {Xc Xc' X : C} [IsCofibrant Xc] [IsCofibrant Xc']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X) [WeakEquivalence pX']
    (Y : D) [IsFibrant Y] (f : (HD).obj (L.obj Xc) ⟶ (HD).obj Y) :
    changeReplacement adj pX pX' Y f = (homEquiv adj pX' Y).symm (homEquiv adj pX Y f) := rfl

/-- The entire change-of-replacement function is identity when the original input is the same. -/
theorem changeReplacement_self {Xc X : C} [IsCofibrant Xc]
    (pX : Xc ⟶ X) [WeakEquivalence pX] (Y : D) [IsFibrant Y] :
    changeReplacement adj pX pX Y = Equiv.refl _ := by
  apply Equiv.ext
  intro f
  exact (homEquiv adj pX Y).symm_apply_apply f

/-- Full changes of three provided replacements compose with their original inverse functions. -/
theorem changeReplacement_trans {Xc Xc' Xc'' X : C}
    [IsCofibrant Xc] [IsCofibrant Xc'] [IsCofibrant Xc'']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X) [WeakEquivalence pX']
    (pX'' : Xc'' ⟶ X) [WeakEquivalence pX''] (Y : D) [IsFibrant Y] :
    (changeReplacement adj pX pX' Y).trans (changeReplacement adj pX' pX'' Y) =
      changeReplacement adj pX pX'' Y := by
  apply Equiv.ext
  intro f
  change (homEquiv adj pX'' Y).symm
    (homEquiv adj pX' Y ((homEquiv adj pX' Y).symm (homEquiv adj pX Y f))) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The full inverse change is exactly the same actual provided pair in the other order. -/
theorem changeReplacement_symm {Xc Xc' X : C} [IsCofibrant Xc] [IsCofibrant Xc']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X) [WeakEquivalence pX']
    (Y : D) [IsFibrant Y] :
    (changeReplacement adj pX pX' Y).symm = changeReplacement adj pX' pX Y := rfl

/-- The two full changed Hom functions are natural in every actual fibrant target map. -/
theorem changeReplacement_target {Xc Xc' X : C} [IsCofibrant Xc] [IsCofibrant Xc']
    (pX : Xc ⟶ X) [WeakEquivalence pX] (pX' : Xc' ⟶ X) [WeakEquivalence pX']
    {Y Y' : D} [IsFibrant Y] [IsFibrant Y']
    (f : (HD).obj (L.obj Xc) ⟶ (HD).obj Y) (g : Y ⟶ Y') :
    changeReplacement adj pX pX' Y' (f ≫ (HD).map g) =
      changeReplacement adj pX pX' Y f ≫ (HD).map g := by
  rw [changeReplacement_apply, changeReplacement_apply,
    homEquiv_target, homEquiv_symm_target]

/-- The original model's resolution gives both complete Hom functions for every coefficient. -/
def canonicalHomEquiv (X : C) (Y : D) [IsFibrant Y] :
    ((HD).obj (L.obj (CofibrantObject.HoCat.resolutionObj X)) ⟶ (HD).obj Y) ≃
      ((HC).obj X ⟶ (HC).obj (R.obj Y)) :=
  homEquiv adj (CofibrantObject.HoCat.pResolutionObj X) Y

/-- The forward canonical function uses the actual resolution inverse and original adjunct. -/
theorem canonicalHomEquiv_apply (X : C) (Y : D) [IsFibrant Y]
    (f : (HD).obj (L.obj (CofibrantObject.HoCat.resolutionObj X)) ⟶ (HD).obj Y) :
    canonicalHomEquiv adj X Y f =
      (replacementHoIso (CofibrantObject.HoCat.pResolutionObj X)).inv ≫
        QuillenOrdinaryHoHom.homEquiv adj (CofibrantObject.HoCat.resolutionObj X) Y f := rfl

/-- The entire inverse canonical function uses the same actual resolution before inverse adjunct. -/
theorem canonicalHomEquiv_symm_apply (X : C) (Y : D) [IsFibrant Y]
    (f : (HC).obj X ⟶ (HC).obj (R.obj Y)) :
    (canonicalHomEquiv adj X Y).symm f =
      (QuillenOrdinaryHoHom.homEquiv adj (CofibrantObject.HoCat.resolutionObj X) Y).symm
        ((HC).map (CofibrantObject.HoCat.pResolutionObj X) ≫ f) := rfl

end HomotopicalAlgebra.QuillenOrdinaryHoReplacement
