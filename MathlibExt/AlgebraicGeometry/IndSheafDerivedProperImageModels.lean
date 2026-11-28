/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived

/-!
# Native derivation of the actual compact-generator proper image

This development specializes native cochain action and total right
 derivation to the source-normalized compact-Yoneda Kan extension.
Source: D'Agnolo--Kashiwara1311.2374v2, Section3.3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CompactSupportIndSheaves
variable (k : Type) [Field k] {X Y : TopCat.{0}} (f : X ⟶ Y)
  (P : CompactPushforwardSource k f)
  [CompactSheafSource k X] [CompactSheafSource k Y]

/-- Match the cochain zero morphisms to the native abelian Ind structure. -/
local instance indAbelianPreadditive (Z : TopCat.{0}) [CompactSheafSource k Z] :
    Preadditive (IndSheaf k Z) :=
  Abelian.toPreadditive

variable (D : IndPushforwardSource k f P) [(indProperImage k f P D).Additive]
attribute [local instance] HasDerivedCategory.standard

universe vA uA vB uB

/-- Native cochain action followed by localization, written before specializing the ind coefficient objects. -/
def beforeRightDerivation {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive] :
    CochainComplex A ℤ ⥤ DerivedCategory B :=
  F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q

/-- The native cochain operator before its canonical total right derivation. -/
def pushforwardBeforeDeriving :
    CochainComplex (IndSheaf k X) ℤ ⥤ IndDerived k Y :=
  beforeRightDerivation (A := IndSheaf k X) (B := IndSheaf k Y)
    (indProperImage k f P D)

structure DerivedIndPushforwardSource : Prop where
  hasDerived : (pushforwardBeforeDeriving k f P D).HasRightDerivedFunctor
    (HomologicalComplex.quasiIso (IndSheaf k X) (.up ℤ))

/-- The source-normalized actual derived direct image. -/
def derivedIndProperImage (H : DerivedIndPushforwardSource k f P D) :
    IndDerived k X ⥤ IndDerived k Y :=
  letI := H.hasDerived
  (pushforwardBeforeDeriving k f P D).totalRightDerived DerivedCategory.Q
    (HomologicalComplex.quasiIso (IndSheaf k X) (.up ℤ))

end MathlibExt.AlgebraicGeometry.IndSheafPushforwardModels
