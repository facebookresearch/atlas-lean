/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafCoefficientModels
public import MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
public import MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

/-!
# Original ordinary iota on native bounded derived sheaves

This is iota, the original restricted-Yoneda embedding of ordinary
coefficient sheaves. It is separate from the left-beta used for ordinary
ring modules. The exact cochain action is localized at native Q, with
boundedness as a separate source proof.
Source: DK1311.2374v2 Section2.2; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinaryIndDerivedModels

open _root_.CategoryTheory TopologicalSpace
open CompactSupportIndSheaves IndSheafCoefficientModels
open MathlibExt.CategoryTheory.NativeBoundedBimoduleModels
open MathlibExt.CategoryTheory.NativeRingedAdjointImageModels

variable (k : Type) [Field k] (X : TopCat.{0})
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} k)]
  [CompactSheafSource k X]

local instance iotaIndPreadditive : Preadditive (IndSheaf k X) := Abelian.toPreadditive
local instance iotaOrdinaryPreadditive : Preadditive (OrdinarySheaf k X) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable (I : OrdinaryIndSource k X) [(ordinaryToInd k X I).Additive]
  (E : ExactImageSource (ordinaryToInd k X I))

def derivedIota : DerivedCategory (OrdinarySheaf k X) ⥤ IndDerived k X :=
  derivedExactImage (ordinaryToInd k X I) E

abbrev BoundedOrdinary := (IsBoundedDerived (OrdinarySheaf k X)).FullSubcategory

structure BoundedIotaSource : Prop where
  bounded : ∀ K : BoundedOrdinary k X, IsBounded k X ((derivedIota k X I E).obj K.obj)

def boundedIota (B : BoundedIotaSource k X I E) : BoundedOrdinary k X ⥤ BoundedIndDerived k X where
  obj K := ⟨(derivedIota k X I E).obj K.obj, B.bounded K⟩
  map f := ObjectProperty.homMk ((derivedIota k X I E).map f.hom)
  map_id K := by apply ObjectProperty.hom_ext; exact (derivedIota k X I E).map_id K.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (derivedIota k X I E).map_comp f.hom g.hom

end MathlibExt.AlgebraicGeometry.OrdinaryIndDerivedModels
