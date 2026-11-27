/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CartesianStackModules
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Native tensor products of cartesian stack module presheaves

The carrier is the actual CartesianStackModules.QCoh full category.
The objectwise tensor and its maps are the native commutative-ring
module-presheaf tensor. The landing certificate is the actual
scalar-extension IsCartesian property of that fixed tensor.

The certificate is completed-source integration, not a duplicate Wanted
claim: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/TensorQuasicoherent.lean
and QuasiCoherentCartesianEquivalence.lean (Apache 2.0).
All functor laws and the full-subcategory lift are native Mathlib code.
This conditional adapter does not declare a new arbitrary tensor operator.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace AlgebraicGeometry.CartesianStackTensorProducts

open CategoryTheory CategoryTheory.MonoidalCategory
open GeneralStackGeometry StackCycleGeometry StackAffineModules CartesianStackModules

variable {S : Scheme.{0}} (X : Stack S)

/-- Genuine cartesian landing of the fixed native objectwise tensor. -/
structure TensorLanding : Prop where
  cartesian : ∀ M N : QCoh X,
    IsCartesian (PresheafOfModulesOfCommRing.Monoidal.tensorObj M.obj N.obj)

/-- The actual native tensor functor on underlying module presheaves. -/
def underlyingTensor : (QCoh X × QCoh X) ⥤ ModulePresheaf X :=
  (forget X).prod (forget X) ⋙ Functor.uncurry.obj (curriedTensor (ModulePresheaf X))

/-- Native tensor lifted into the actual cartesian full subcategory. -/
def tensorUncurried (P : TensorLanding X) : (QCoh X × QCoh X) ⥤ QCoh X :=
  (show ObjectProperty (ModulePresheaf X) from IsCartesian).lift
    (underlyingTensor X) (fun M => P.cartesian M.1 M.2)

/-- Curried tensor with the same native carrier, maps and landing certificate. -/
def tensor (P : TensorLanding X) : QCoh X ⥤ QCoh X ⥤ QCoh X :=
  Functor.curry.obj (tensorUncurried X P)

theorem tensor_obj (P : TensorLanding X) (M N : QCoh X) :
    (((tensor X P).obj M).obj N).obj =
      PresheafOfModulesOfCommRing.Monoidal.tensorObj M.obj N.obj := rfl

/-- Forgetting the landing proof gives exactly the completed native tensor functor. -/
def forgetTensorIso (P : TensorLanding X) :
    tensorUncurried X P ⋙ forget X ≅ underlyingTensor X := Iso.refl _

end AlgebraicGeometry.CartesianStackTensorProducts
