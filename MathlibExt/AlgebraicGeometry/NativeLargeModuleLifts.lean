/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels

/-!
# Native homogeneous coefficient lifting for full DG modules

The homogeneous cochain map is the native componentwise map under the
same coefficient lift used by the derived QCoh enhancement. A full
module lift fixes every actual module value and every homogeneous
action. Its endomorphism map is normalized at every original module
index and every integer degree. No geometric RHom or tangent formula
is included in this coefficient-universe construction.

References: the native DG/module and universe-lift source constructors
retained in the imported modules; Toen--Vaquie math/0503269v5, Section3.5
for the locally small geometric Hom convention.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open CochainComplex.HomComplex

universe u

variable (k : Type u) [CommRing k]

/-- The original termwise module lift followed by the actual coefficient ring equivalence. -/
def coefficientLift : ModuleCat.{u} k ⥤ ModuleCat.{u + 1} (LargeScalar k) :=
  liftModules k ⋙ ModuleCat.restrictScalars (ULift.ringEquiv : LargeScalar k ≃+* k).toRingHom

instance coefficientLift_additive : (coefficientLift k).Additive where
  map_add {M N} f g := by
    ext x
    rfl

/-- Every homogeneous cochain keeps its original components, with the same actual coefficient lift. -/
def homogeneousLift {F G : Cochains k} {n : ℤ} (a : Cochain F G n) :
    Cochain ((largeCochainLift k).obj F) ((largeCochainLift k).obj G) n :=
  a.map (coefficientLift k)

/-- Its actual component acts by the original component on the original coefficient. -/
theorem homogeneousLift_component {F G : Cochains k} {n i j : ℤ} (h : i + n = j)
    (a : Cochain F G n) (x : F.X i) :
    ((homogeneousLift k a).v i j h).hom (ULift.up x) = ULift.up ((a.v i j h).hom x) := rfl

variable {k} (C : CochainLiftModel k) (T : DGCat k) (M : RightModule k T)

/-- A whole actual projective-module lift is fixed at every original index and every homogeneous action. -/
structure LargeProjectiveModuleLift where
  module : DGDerivedModules (LargeScalar k) (liftedDGCategory C T)
  value_eq : ∀ x : Tᵒᵖ,
    module.obj.toEnrichedFunctor.obj (op (ULift.up x.unop)) =
      (largeCochainLift k).obj (M.toEnrichedFunctor.obj x)
  action_eq : ∀ (x y : Tᵒᵖ) (n : ℤ) (a : DGHom k n x y),
    HEq (module.obj.toEnrichedFunctor.dgMap n
      (X := op (ULift.up x.unop)) (Y := op (ULift.up y.unop)) (ULift.up a))
      (homogeneousLift k (M.toEnrichedFunctor.dgMap n (X := x) (Y := y) a))
  endomorphismMap : (largeCochainLift k).obj (dgHomComplex k M M) ⟶
    dgHomComplex (LargeScalar k) module.obj module.obj
  endomorphism_normalized : ∀ (n : ℤ) (a : DGHom k n M M) (x : Tᵒᵖ),
    HEq (DGFunctor.dgApp (LargeScalar k) (C := (liftedDGCategory C T)ᵒᵖ) n
      (op (ULift.up x.unop : liftedDGCategory C T))
      ((endomorphismMap.f n).hom (ULift.up a)))
      (homogeneousLift k (DGFunctor.dgApp k n x a))

end MathlibExt.AlgebraicGeometry.NativeLargeModuleLifts
