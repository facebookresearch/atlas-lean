/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# The actual bounded Ind tensor from native cochain totalization

The termwise bounded source consists of original Ind complexes, with
actual quasi-isomorphisms. Its functor into bounded derived Ind is the
original Q on objects and maps. The tensor is the native signed total
complex of the fixed compact-generator Ind tensor. Localization then
gives the tensor on the original bounded derived category.

Only structural existence, boundedness and localization properties are
source inputs. No arbitrary derived tensor object or functor is chosen,
and no claim about all unbounded tensor complexes is made.

Source: D'Agnolo--Kashiwara1311.2374v2, Sections2.2 and3.3;
Kashiwara--Schapira, Ind-sheaves. Native cochain totalization and
localization are Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Apache2.0, Joël Riou and the Mathlib contributors.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CompactSupportIndSheaves IndSheafCoefficientModels

variable (k : Type) [Field k] (X : TopCat.{0}) [CompactSheafSource k X]
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]

/-- Use the zero morphisms of the same native abelian category as Q. -/
local instance tensorAbelianPreadditive : Preadditive (IndSheaf k X) := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- Literal boundedness of the terms of the original cochain complex. -/
def termwiseBounded : ObjectProperty (CochainComplex (IndSheaf k X) ℤ) := fun K =>
  ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)

/-- The complete bounded-cochain carrier, with every original cochain morphism. -/
abbrev BoundedIndComplex := (termwiseBounded k X).FullSubcategory

/-- Its weak maps are the original cochain quasi-isomorphisms. -/
def boundedQuasiIso : MorphismProperty (BoundedIndComplex k X) :=
  (HomologicalComplex.quasiIso (IndSheaf k X) (.up ℤ)).inverseImage (termwiseBounded k X).ι

instance boundedQuasiIso_containsIdentities : (boundedQuasiIso k X).ContainsIdentities :=
  inferInstanceAs (((HomologicalComplex.quasiIso (IndSheaf k X) (.up ℤ)).inverseImage
    (termwiseBounded k X).ι).ContainsIdentities)

/-- Ordinary bounded terms have bounded cohomology under the original Q. -/
structure BoundedCohomologySource : Prop where
  bounded : ∀ K : BoundedIndComplex k X, IsBounded k X (DerivedCategory.Q.obj K.obj)

/-- The original Q, with its true bounded-source and bounded-cohomology targets. -/
def boundedQ (R : BoundedCohomologySource k X) :
    BoundedIndComplex k X ⥤ BoundedIndDerived k X where
  obj K := ⟨DerivedCategory.Q.obj K.obj, R.bounded K⟩
  map f := ObjectProperty.homMk (DerivedCategory.Q.map f.hom)
  map_id K := by apply ObjectProperty.hom_ext; exact DerivedCategory.Q.map_id K.obj
  map_comp f g := by apply ObjectProperty.hom_ext; exact DerivedCategory.Q.map_comp f.hom g.hom

/-- The localization property concerns exactly that fixed bounded Q. -/
structure BoundedLocalizationSource (R : BoundedCohomologySource k X) : Prop where
  isLocalization : (boundedQ k X R).IsLocalization (boundedQuasiIso k X)

variable (S : CompactTensorSource k X) (D : IndTensorSource k X S)

/-- Curry the same actual compact-Yoneda Ind tensor. -/
def tensorCurried : IndSheaf k X ⥤ IndSheaf k X ⥤ IndSheaf k X :=
  Functor.curry.obj (indTensor k X S D)

/-- Structural additive and totalization inputs on the prescribed Ind tensor. -/
class TensorCochainSource : Prop where
  [leftAdditive : (tensorCurried k X S D).Additive]
  [rightAdditive : ∀ N : IndSheaf k X, ((tensorCurried k X S D).obj N).Additive]
  [total : ∀ K L : CochainComplex (IndSheaf k X) ℤ,
    HomologicalComplex.HasMapBifunctor K L (tensorCurried k X S D) (.up ℤ)]

attribute [instance] TensorCochainSource.leftAdditive TensorCochainSource.rightAdditive
  TensorCochainSource.total

variable [TensorCochainSource k X S D]

/-- The native signed total cochain tensor, on all original homogeneous objects and maps. -/
def cochainTensor :
    CochainComplex (IndSheaf k X) ℤ ⥤ CochainComplex (IndSheaf k X) ℤ ⥤
      CochainComplex (IndSheaf k X) ℤ :=
  (tensorCurried k X S D).map₂CochainComplex

/-- Boundedness refers to the terms of this actual total cochain tensor. -/
structure BoundedTensorSource : Prop where
  bounded : ∀ K L : BoundedIndComplex k X,
    termwiseBounded k X (((cochainTensor k X S D).obj K.obj).obj L.obj)

/-- The original cochain tensor, now on its full bounded source and target. -/
def boundedCochainTensor (T : BoundedTensorSource k X S D) :
    BoundedIndComplex k X × BoundedIndComplex k X ⥤ BoundedIndComplex k X :=
  ObjectProperty.lift (termwiseBounded k X)
    (((termwiseBounded k X).ι.prod (termwiseBounded k X).ι) ⋙
      Functor.uncurry.obj (cochainTensor k X S D))
    (fun KL ↦ T.bounded KL.1 KL.2)

/-- The prescribed tensor followed by the original bounded Q. -/
def tensorBeforeDeriving (R : BoundedCohomologySource k X) (T : BoundedTensorSource k X S D) :
    BoundedIndComplex k X ⥤ BoundedIndComplex k X ⥤ BoundedIndDerived k X :=
  Functor.curry.obj (boundedCochainTensor k X S D T ⋙ boundedQ k X R)

/-- The actual bounded tensor inverts exactly the original bounded quasi-isomorphisms. -/
structure DerivedTensorSource (R : BoundedCohomologySource k X)
    (T : BoundedTensorSource k X S D) : Prop where
  inverts : MorphismProperty.IsInvertedBy₂ (boundedQuasiIso k X) (boundedQuasiIso k X)
    (tensorBeforeDeriving k X S D R T)

/-- The actual bounded derived tensor is the native localization of that fixed signed total complex. -/
def derivedTensor (R : BoundedCohomologySource k X) (L : BoundedLocalizationSource k X R)
    (T : BoundedTensorSource k X S D) (E : DerivedTensorSource k X S D R T) :
    BoundedIndDerived k X ⥤ BoundedIndDerived k X ⥤ BoundedIndDerived k X :=
  letI := L.isLocalization
  Localization.lift₂ (tensorBeforeDeriving k X S D R T) E.inverts
    (boundedQ k X R) (boundedQ k X R)

end MathlibExt.AlgebraicGeometry.IndSheafBoundedTensorModels
