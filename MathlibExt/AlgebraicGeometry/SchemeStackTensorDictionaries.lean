/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CartesianStackTensorComparisons
public import MathlibExt.AlgebraicGeometry.SchemeStackModuleModels
public import MathlibExt.AlgebraicGeometry.NativeTensorComparisons

/-!
# Tensor dictionaries fixed on every actual affine section

The tensor section map is the native module-presheaf tensor followed by
the actual sheafification unit. The represented-stack tensor comparison
and its unit are fixed on every affine test scheme and all pure tensors,
using the already normalized full QCoh/module dictionary.

This is source integration of the credited AxiomMath/Stacks cartesian,
represented-QCoh and tensor implementations; no root/parabolic theorem
is assumed in these dictionary types.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.SchemeStackTensorDictionaries

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackAffineModules _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.CartesianStackTensorProducts _root_.AlgebraicGeometry.SchemeStackModuleModels
open AlgebraicLineBundleFamilies CoherentCurveLinearSeries LineBundleTaskContracts
open NativeTensorComparisons ModuleTensorPullbackSections
open scoped TensorProduct

universe u

/-- The real sheafification map on a pure tensor of actual global sections. -/
def tensorSections (Y : Scheme.{u}) (L M : Y.Modules) (x : Γ(L,⊤)) (y : Γ(M,⊤)) :
    Γ(moduleTensor Y L M,⊤) :=
  let P := PresheafOfModulesOfCommRing.{u} Y.sheaf.obj
  let C : P := ((curriedTensor P).obj ((forgetModules Y).obj L)).obj ((forgetModules Y).obj M)
  (((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit.app C).app (op ⊤)) (x ⊗ₜ y)

variable {S : Scheme.{0}} {Y : Over S} (R : SchemeStackModuleModels.Model Y)
  (K : ModuleDictionary R) (T : TensorLanding R.stack)

/-- Source tensor integration on the same represented scheme and native
cartesian module tensor, specified on every coefficient generator. -/
structure TensorDictionary where
  tensor : ∀ M N : QCoh R.stack,
    K.toModules.obj (((CartesianStackTensorProducts.tensor R.stack T).obj M).obj N) ≅
      moduleTensor Y.left (K.toModules.obj M) (K.toModules.obj N)
  pullbackTensor : ∀ a : AffinePoint R.stack, PullbackTensorData (R.testMap a)
  tensor_normalized : ∀ (M N : QCoh R.stack) (a : AffinePoint R.stack)
    (x : M.obj.obj (op a)) (y : N.obj.obj (op a)),
    ((((pullbackTensor a).comparison (K.toModules.obj M) (K.toModules.obj N)).hom.val.app (op ⊤)).hom)
      (((((Scheme.Modules.pullback (R.testMap a)).map (tensor M N).hom).val.app (op ⊤)).hom)
        (K.sections (((CartesianStackTensorProducts.tensor R.stack T).obj M).obj N) a (x ⊗ₜ y))) =
    tensorSections a.obj.base.left
      ((Scheme.Modules.pullback (R.testMap a)).obj (K.toModules.obj M))
      ((Scheme.Modules.pullback (R.testMap a)).obj (K.toModules.obj N))
      (K.sections M a x) (K.sections N a y)
  unit : K.toModules.obj (CartesianStackModules.structureModule R.stack) ≅ structureModule Y.left
  unit_normalized : ∀ (a : AffinePoint R.stack) (r : Γ(a.obj.base.left,⊤)),
    ((SheafOfModules.pullbackObjUnitToUnit (R.testMap a).toRingCatSheafHom).val.app (op ⊤)).hom
      (((((Scheme.Modules.pullback (R.testMap a)).map unit.hom).val.app (op ⊤)).hom)
        (K.sections (CartesianStackModules.structureModule R.stack) a r)) = r

end MathlibExt.AlgebraicGeometry.SchemeStackTensorDictionaries
