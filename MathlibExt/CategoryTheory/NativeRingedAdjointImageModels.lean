/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeMonoidalBimoduleMapping
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Ringed proper images fixed by the original inverse/proper adjunction

The projection maps are computed from the original monoidal inverse
image and its native counit. Both ring actions are transported through
those maps. The ringed image retains every actual underlying object/map;
its derived image is the native total right derivation of that exact
cochain action. This supplies i!! and its right adjoint i! on ringed Ind
objects, including the commuting X-action in the P calculation.

Source: DK1311.2374v2 Sections3.3,4.10,8.2; Mathlib56a005 native
monoidal adjunction and totalRightDerived constructors, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe uC uD vC vD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [MonoidalCategory C] [MonoidalCategory D]
  (inverse : D ⥤ C) [inverse.Monoidal] (proper : C ⥤ D) (adj : inverse ⊣ proper)

def leftProjectionMap (A : D) (F : C) :
    A ⊗ proper.obj F ⟶ proper.obj (inverse.obj A ⊗ F) :=
  (adj.homEquiv _ _)
    ((Functor.Monoidal.μIso inverse A (proper.obj F)).inv ≫
      (𝟙 (inverse.obj A) ⊗ₘ adj.counit.app F))

def rightProjectionMap (A : D) (F : C) :
    proper.obj F ⊗ A ⟶ proper.obj (F ⊗ inverse.obj A) :=
  (adj.homEquiv _ _)
    ((Functor.Monoidal.μIso inverse (proper.obj F) A).inv ≫
      (adj.counit.app F ⊗ₘ 𝟙 (inverse.obj A)))

variable (R S : Mon C) (R' S' : Mon D)
  (RI : inverse.mapMon.obj R' ≅ R) (SI : inverse.mapMon.obj S' ≅ S)

/-- Both native actions and all maps are fixed by the original projection mates. -/
structure RingedImageSource where
  functor : Bimod R S ⥤ Bimod R' S'
  underlying : functor ⋙ Bimod.forget (B := S') R' ≅ Bimod.forget (B := S) R ⋙ proper
  leftAction : ∀ M : Bimod R S,
    (functor.obj M).actLeft ≫ underlying.hom.app M =
      (𝟙 R'.X ⊗ₘ underlying.hom.app M) ≫ leftProjectionMap inverse proper adj R'.X M.X ≫
        proper.map ((RI.hom.hom ⊗ₘ 𝟙 M.X) ≫ M.actLeft)
  rightAction : ∀ M : Bimod R S,
    (functor.obj M).actRight ≫ underlying.hom.app M =
      (underlying.hom.app M ⊗ₘ 𝟙 S'.X) ≫ rightProjectionMap inverse proper adj S'.X M.X ≫
        proper.map ((𝟙 M.X ⊗ₘ SI.hom.hom) ≫ M.actRight)

section Derived

variable {A : Type uC} {B : Type uD} [Category.{vC} A] [Category.{vD} B]
  [Abelian A] [Abelian B]

local instance imageSourcePreadditive : Preadditive A := Abelian.toPreadditive
local instance imageTargetPreadditive : Preadditive B := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (F : A ⥤ B) [F.Additive]

def unaryBeforeDeriving : CochainComplex A ℤ ⥤ DerivedCategory B :=
  F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

structure RightDerivationSource : Prop where
  hasDerived : (unaryBeforeDeriving F).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso A (.up ℤ))

def derivedImage (S : RightDerivationSource F) : DerivedCategory A ⥤ DerivedCategory B :=
  letI := S.hasDerived
  (unaryBeforeDeriving F).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))

structure ExactImageSource : Prop where
  inverts : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy (unaryBeforeDeriving F)

def derivedExactImage (S : ExactImageSource F) : DerivedCategory A ⥤ DerivedCategory B :=
  Localization.lift (unaryBeforeDeriving F) S.inverts DerivedCategory.Q

end Derived
end MathlibExt.CategoryTheory.NativeRingedAdjointImageModels
