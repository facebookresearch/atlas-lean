/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.CategoryTheory.NativeDerivedBimoduleOperators
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Actual bounded native bimodule derived categories and coefficient forgetting

Objects and boundedness are measured by native derived homology.
The coefficient map is the actual Bimod forget functor on cochains,
localized at the original quasi-isomorphisms. Structural exactness and
boundedness are separate source proof requests.

Source: DK1311.2374v2 Section4.10; Mathlib56a005 native Bimod,
cochain Q and Localization.lift, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeBoundedBimoduleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [∀ R S : Mon C, Abelian (Bimod R S)]

local instance coefficientPreadditive : Preadditive C := Abelian.toPreadditive
local instance bimodulePreadditive (R S : Mon C) : Preadditive (Bimod R S) :=
  Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

def IsBoundedDerived (A : Type u) [Category.{v} A] [Abelian A] :
    ObjectProperty (DerivedCategory A) := fun K =>
  ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
    IsZero ((DerivedCategory.homologyFunctor A n).obj K)

abbrev BoundedModules (R S : Mon C) := (IsBoundedDerived (Bimod R S)).FullSubcategory

variable (R S : Mon C) [(Bimod.forget (B := S) R).Additive]

def coefficientBeforeDeriving : CochainComplex (Bimod R S) ℤ ⥤ DerivedCategory C :=
  (Bimod.forget (B := S) R).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

structure ExactCoefficientSource : Prop where
  inverts : (HomologicalComplex.quasiIso (Bimod R S) (.up ℤ)).IsInvertedBy
    (coefficientBeforeDeriving R S)

def derivedCoefficients (E : ExactCoefficientSource R S) :
    DerivedCategory (Bimod R S) ⥤ DerivedCategory C :=
  Localization.lift (coefficientBeforeDeriving R S) E.inverts DerivedCategory.Q

def coefficientComparison (E : ExactCoefficientSource R S) :
    DerivedCategory.Q ⋙ derivedCoefficients R S E ≅ coefficientBeforeDeriving R S :=
  Localization.fac (coefficientBeforeDeriving R S) E.inverts DerivedCategory.Q

structure BoundedCoefficientSource (E : ExactCoefficientSource R S) : Prop where
  bounded : ∀ K : BoundedModules R S,
    IsBoundedDerived C ((derivedCoefficients R S E).obj K.obj)

def boundedCoefficients (E : ExactCoefficientSource R S) (B : BoundedCoefficientSource R S E) :
    BoundedModules R S ⥤ (IsBoundedDerived C).FullSubcategory where
  obj K := ⟨(derivedCoefficients R S E).obj K.obj, B.bounded K⟩
  map f := ObjectProperty.homMk ((derivedCoefficients R S E).map f.hom)
  map_id K := by apply ObjectProperty.hom_ext; exact (derivedCoefficients R S E).map_id K.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (derivedCoefficients R S E).map_comp f.hom g.hom

end MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
