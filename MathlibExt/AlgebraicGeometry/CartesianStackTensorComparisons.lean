/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CartesianStackTensorProducts
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Native cartesian tensor structure and adjunction tensor maps

The monoidal structure is the native full monoidal subcategory of actual
module presheaves, using the already source-covered Cartesian landing
certificate. Pullback tensor comparison is the same literal module
precomposition on every affine point. The direct-image tensor map and
projection-formula map are their actual adjunction mates involving the
native counit; they are not unconstrained asserted comparison maps.

Source: the AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b
cartesian/QCoh tensor and direct-image adapters credited in the imports
(Apache License 2.0); Mathlib monoidal subcategories and adjunctions.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CartesianStackTensorComparisons

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackAffineModules _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.CartesianStackTensorProducts

variable {S : Scheme.{0}} (R : Stack S) (T : TensorLanding R)

def monoidalProperty : (show ObjectProperty (ModulePresheaf R) from IsCartesian).IsMonoidal where
  prop_unit := unit_cartesian R
  prop_tensor M N hM hN := T.cartesian ⟨M,hM⟩ ⟨N,hN⟩

/-- All objects, arrows and coherence maps come from the native presheaf tensor. -/
def monoidal : MonoidalCategory (QCoh R) := by
  letI := monoidalProperty R T
  infer_instance

variable {R} {Z : Stack S} (f : StackHom R Z) (U : TensorLanding Z)

/-- Native module pullback commutes with this very tensor on every affine test. -/
def pullbackTensor (M N : QCoh Z) :
    (pullback f).obj (((tensor Z U).obj M).obj N) ≅
      ((tensor R T).obj ((pullback f).obj M)).obj ((pullback f).obj N) := Iso.refl _

variable (Q : DirectImage f)

/-- The actual right-adjoint lax tensor map, fixed by the native counit. -/
def directImageTensor (M N : QCoh R) :
    ((tensor Z U).obj (Q.functor.obj M)).obj (Q.functor.obj N) ⟶
      Q.functor.obj (((tensor R T).obj M).obj N) :=
  (Q.adjunction.homEquiv _ _)
    ((pullbackTensor T f U (Q.functor.obj M) (Q.functor.obj N)).hom ≫
      (tensorUncurried R T).map (Q.adjunction.counit.app M, Q.adjunction.counit.app N))

/-- The source projection-formula map is the adjunction mate of pullback
tensor followed by the actual counit on the right-hand module. -/
def projectionFormula (L : QCoh Z) (M : QCoh R) :
    ((tensor Z U).obj L).obj (Q.functor.obj M) ⟶
      Q.functor.obj (((tensor R T).obj ((pullback f).obj L)).obj M) :=
  (Q.adjunction.homEquiv _ _)
    ((pullbackTensor T f U L (Q.functor.obj M)).hom ≫
      (tensorUncurried R T).map (𝟙 ((pullback f).obj L), Q.adjunction.counit.app M))

end MathlibExt.AlgebraicGeometry.CartesianStackTensorComparisons
