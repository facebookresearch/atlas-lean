/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Monoidal.Bimod.OppositeTensor
public import MathlibExt.CategoryTheory.Monoidal.Bimod.TensorHomParametrized

/-!
# The other original relative bimodule Hom

The complete opposite bimodule equivalence and the actual opposite tensor
comparison transport the right tensor-Hom adjunction to the fixed-left
tensor. Its relative Hom retains both original outer actions through the
proved inverse presentation. Every target and contravariant source map is
the image of its actual opposite relative-Hom map.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalOpposite MonObj Opposite
open scoped MonoidalCategory

namespace Bimod.InternalHom

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalClosed C] [HasLimitsOfSize.{0, 0} C] [HasColimitsOfSize.{0, 0} C]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] {A B D : Mon C}

/-- The chosen closed structure on the monoidal opposite for transporting the left relative Hom. -/
local instance leftOppositeClosed : MonoidalClosed Cᴹᵒᵖ := monoidalClosedOpposite (C := C)
local instance leftOppositeColimits : HasColimitsOfSize.{0, 0} Cᴹᵒᵖ := Bimod.oppositeTensorColimits
local instance leftOppositeLeftPreserves (X : Cᴹᵒᵖ) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft X) := Bimod.oppositeTensorLeftPreserves X
local instance leftOppositeRightPreserves (X : Cᴹᵒᵖ) :
    PreservesColimitsOfSize.{0, 0} (tensorRight X) := Bimod.oppositeTensorRightPreserves X
local instance leftOppositeLimits : HasLimitsOfSize.{0, 0} Cᴹᵒᵖ := by
  let : (CategoryTheory.unmopFunctor C).IsEquivalence := (unmopEquiv C).isEquivalence_functor
  let : CreatesLimitsOfSize.{0, 0} (CategoryTheory.unmopFunctor C) :=
    Functor.createsLimitsOfIsEquivalence _
  exact hasLimits_of_hasLimits_createsLimits (CategoryTheory.unmopFunctor C)

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The original left relative Hom is the complete opposite relative Hom under the actual inverse presentation. -/
def leftHomFunctor (M : Bimod A B) : Bimod A D ⥤ Bimod B D :=
  (mopEquivalence A D).functor ⋙
    homFunctor (A := mopMon D) (mopBimodule M) ⋙ (mopEquivalence B D).inverse

/-- The entire fixed-left tensor is the original transported opposite fixed-right tensor. -/
def leftTensorComparison (M : Bimod A B) :
    Bimod.mopFunctor B D ⋙ tensorRightFunctor (A := mopMon D) (mopBimodule M) ⋙ Bimod.unmopFunctor A D ≅
      tensorLeftFunctor (D := D) M :=
  Functor.isoWhiskerRight (mopTensorLeftNatIso M).symm (Bimod.unmopFunctor A D) ≪≫
    Functor.isoWhiskerLeft (tensorLeftFunctor M) (mopEquivalence A D).unitIso.symm

/-- The actual fixed-left tensor has the original opposite relative Hom as its complete right adjoint. -/
def leftTensorHomAdjunction (M : Bimod A B) : tensorLeftFunctor (D := D) M ⊣ leftHomFunctor M :=
  (((mopEquivalence B D).toAdjunction.comp
      (tensorHomAdjunction (A := mopMon D) (mopBimodule M))).comp
        (mopEquivalence A D).symm.toAdjunction).ofNatIsoLeft (leftTensorComparison M)

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every original contravariant left bimodule map retains the original opposite pre-map. -/
def leftHomPre {M M' : Bimod A B} (f : M ⟶ M') (P : Bimod A D) :
    (leftHomFunctor M').obj P ⟶ (leftHomFunctor M).obj P :=
  (Bimod.unmopFunctor B D).map (homPre (mopBimoduleMap f) (mopBimodule P))

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every original source identity acts identically on the complete left relative Hom. -/
theorem leftHomPre_id (M : Bimod A B) (P : Bimod A D) :
    leftHomPre (𝟙 M) P = 𝟙 ((leftHomFunctor M).obj P) := by
  have hi : mopBimoduleMap (𝟙 M) = 𝟙 (mopBimodule M) := by apply Bimod.hom_ext; rfl
  rw [leftHomPre, hi, homPre_id]
  exact (Bimod.unmopFunctor B D).map_id _

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every original source composition acts in the actual contravariant order on left relative Hom. -/
theorem leftHomPre_comp {M M' M'' : Bimod A B} (f : M ⟶ M') (g : M' ⟶ M'') (P : Bimod A D) :
    leftHomPre (f ≫ g) P = leftHomPre g P ≫ leftHomPre f P := by
  have hm : mopBimoduleMap (f ≫ g) = mopBimoduleMap f ≫ mopBimoduleMap g := by
    apply Bimod.hom_ext
    rfl
  rw [leftHomPre, hm, homPre_comp, CategoryTheory.Functor.map_comp]
  rfl

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The original source pre-map is natural on every original target bimodule arrow. -/
theorem leftHomPre_naturality {M M' : Bimod A B} (f : M ⟶ M') {P P' : Bimod A D} (g : P ⟶ P') :
    (leftHomFunctor M').map g ≫ leftHomPre f P' = leftHomPre f P ≫ (leftHomFunctor M).map g := by
  have h := congrArg (Bimod.unmopFunctor B D).map
    (homPre_homMap (mopBimoduleMap f) (mopBimoduleMap g))
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h
  exact h

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- Every original left source arrow forms a complete natural transformation on left relative Hom. -/
def leftHomPreNatural {M M' : Bimod A B} (f : M ⟶ M') : leftHomFunctor (D := D) M' ⟶ leftHomFunctor M where
  app := leftHomPre f
  naturality _ _ g := leftHomPre_naturality f g

omit [HasColimitsOfSize.{0, 0} C]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
    [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] in
/-- The other original relative Hom is an actual contravariant-source, covariant-target bifunctor. -/
def leftHomContravariant : (Bimod A B)ᵒᵖ ⥤ Bimod A D ⥤ Bimod B D where
  obj M := leftHomFunctor M.unop
  map f := leftHomPreNatural f.unop
  map_id M := by
    ext P
    exact congrArg Bimod.Hom.hom (leftHomPre_id M.unop P)
  map_comp f g := by
    ext P
    exact congrArg Bimod.Hom.hom (leftHomPre_comp g.unop f.unop P)

end Bimod.InternalHom
