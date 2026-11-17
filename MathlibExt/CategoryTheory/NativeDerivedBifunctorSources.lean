/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Native signed cochain bifunctors and their total left derivation

The cochain functor is the native signed totalization of the fixed
ordinary bifunctor. Its derived operator is its total left derivation
along the pair of original quasi-isomorphism localizations. No exactness
of an underived balanced D-tensor is assumed: resolutions belong to this
universal derived construction.

Source: Mathlib56a005855ea17e0b0958f73ec801ae140b0a1679,
Algebra/Homology/Bifunctor and Functor/Derived/LeftDerived (Joël Riou),
Apache 2.0. DK arXiv:1311.2374v2, Sections 5.2, 8.2, 9.1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.NativeDerivedBifunctorSources

open _root_.CategoryTheory

universe uA uB uC vA vB vC
variable {A : Type uA} {B : Type uB} {C : Type uC}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Abelian A] [Abelian B] [Abelian C] (F : A ⥤ B ⥤ C)

local instance sourcePreadditiveA : Preadditive A := Abelian.toPreadditive
local instance sourcePreadditiveB : Preadditive B := Abelian.toPreadditive
local instance sourcePreadditiveC : Preadditive C := Abelian.toPreadditive

attribute [local instance] HasDerivedCategory.standard

/-- Structural totalization facts for this exact source bifunctor. -/
class CochainSource : Prop where
  [leftAdditive : F.Additive]
  [rightAdditive : ∀ a : A, (F.obj a).Additive]
  [total : ∀ K : CochainComplex A ℤ, ∀ L : CochainComplex B ℤ,
    HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]

attribute [instance] CochainSource.leftAdditive CochainSource.rightAdditive CochainSource.total

variable [CochainSource F]

/-- The original signed total complex, on all cochain objects and maps. -/
def cochainBifunctor : CochainComplex A ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex C ℤ :=
  F.map₂CochainComplex

/-- Quasi-isomorphisms in each actual original source. -/
def pairQuasiIso : MorphismProperty (CochainComplex A ℤ × CochainComplex B ℤ) :=
  fun _ _ f => (HomologicalComplex.quasiIso A (.up ℤ)) f.1 ∧
    (HomologicalComplex.quasiIso B (.up ℤ)) f.2

/-- The two original native derived-category projections. -/
def pairQ : CochainComplex A ℤ × CochainComplex B ℤ ⥤ DerivedCategory A × DerivedCategory B :=
  DerivedCategory.Q.prod DerivedCategory.Q

/-- Original signed cochain tensor followed by the native target Q. -/
def beforeDerivation : CochainComplex A ℤ × CochainComplex B ℤ ⥤ DerivedCategory C :=
  Functor.uncurry.obj (cochainBifunctor F) ⋙ DerivedCategory.Q

/-- Existence/localization concerns only the fixed original total complex. -/
structure LeftDerivationSource : Prop where
  localizes : (pairQ (A := A) (B := B)).IsLocalization (pairQuasiIso (A := A) (B := B))
  hasDerived : (beforeDerivation F).HasLeftDerivedFunctor (pairQuasiIso (A := A) (B := B))

/-- Native total left derivation of the prescribed cochain bifunctor. -/
def derivedBifunctor (S : LeftDerivationSource F) :
    DerivedCategory A ⥤ DerivedCategory B ⥤ DerivedCategory C :=
  letI := S.localizes
  letI := S.hasDerived
  Functor.curry.obj ((beforeDerivation F).totalLeftDerived
    (pairQ (A := A) (B := B)) (pairQuasiIso (A := A) (B := B)))

end MathlibExt.CategoryTheory.NativeDerivedBifunctorSources
