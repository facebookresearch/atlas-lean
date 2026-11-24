/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GlobalParabolicRootModels

/-!
# Native tensor maps for the normalized Phi functor

The tensor component is the actual direct-image lax tensor map followed
by the native root tensor rearrangement and universal root multiplication.
The global comparison is its lift through the actual balanced bilinear
tensor universal property. The unit comparison and the Borne--Vistoli
equivalence are left to a separate development, which needs the parabolic
unit on fixed chart data.
Reference: Borne–Vistoli arXiv:1001.0466v2, Section5.3 and Theorem6.1.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ParabolicRootComparisonMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.CartesianStackModules _root_.AlgebraicGeometry.CartesianStackTensorProducts
open _root_.AlgebraicGeometry.SchemeStackModuleModels
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage
open ParabolicSheafCategories RootWeightEvaluations UniversalRootWeightLines
open RootStackProjectionModules RootWeightTensorModels RootParabolicPeriodModels
open SchemeStackTensorDictionaries ParabolicBilinearTensorModels GlobalParabolicRootModels
open AlgebraicLineBundleFamilies CoherentCurveLinearSeries LineBundleTaskContracts

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (R : DenominatorRootStacks.Model I D j (𝟙 X)) (TG : TensorLanding R.stack)
  (C : EtaleRootData I D j G R) (P : PhiAssembly I D j G R C)

/-- These are equalities of the fixed native module precomposition,
not freely supplied purported structural isomorphisms. -/
structure StructuralRestriction where
  tensor_eq : ∀ (U : X.Etale) (F H : QCoh R.stack),
    (C.restrict U).obj (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H) =
      ((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj ((C.restrict U).obj F)).obj
        ((C.restrict U).obj H)
  unit_eq : ∀ U : X.Etale,
    (C.restrict U).obj (CartesianStackModules.structureModule R.stack) =
      CartesianStackModules.structureModule (C.localRoot U).stack

variable (S : StructuralRestriction I D j G R TG C)

def rootTensorRearrangement (U : X.Etale) (F H : QCoh R.stack)
    (v w : Weight (B.obj.obj (op U))) :
    ((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj
      (((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj ((C.restrict U).obj F)).obj
        ((C.weights U).line.obj v))).obj
      (((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj ((C.restrict U).obj H)).obj
        ((C.weights U).line.obj w)) ≅
    ((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj
      ((C.restrict U).obj (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H))).obj
        ((C.weights U).line.obj (weightProduct v w)) := by
  letI := CartesianStackTensorComparisons.monoidal (C.localRoot U).stack (C.tensor U)
  let F' := (C.restrict U).obj F
  let H' := (C.restrict U).obj H
  let V := (C.weights U).line.obj v
  let W := (C.weights U).line.obj w
  exact (α_ F' V (H' ⊗ W)) ≪≫
    whiskerLeftIso F' (α_ V H' W).symm ≪≫
    whiskerLeftIso F' (whiskerRightIso (β_ V H') W) ≪≫
    whiskerLeftIso F' (α_ H' V W) ≪≫
    (α_ F' H' (V ⊗ W)).symm ≪≫
    whiskerLeftIso (F' ⊗ H') ((C.weightTensor U).multiplication v w) ≪≫
    whiskerRightIso (eqToIso (S.tensor_eq U F H).symm) ((C.weights U).line.obj (weightProduct v w))

def localTensorComponent (U : X.Etale) (F H : QCoh R.stack)
    (v w : Weight (B.obj.obj (op U))) :
    moduleTensor U.left (((C.localPhi U).obj F).obj v) (((C.localPhi U).obj H).obj w) ⟶
      ((C.localPhi U).obj (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H)).obj (weightProduct v w) :=
  ((C.tensorDictionary U).tensor
    ((C.directImage U).functor.obj (((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj
      ((C.restrict U).obj F)).obj ((C.weights U).line.obj v)))
    ((C.directImage U).functor.obj (((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj
      ((C.restrict U).obj H)).obj ((C.weights U).line.obj w)))).inv ≫
  (C.dictionary U).toModules.map (CartesianStackTensorComparisons.directImageTensor (C.tensor U)
    (C.projection U).morphism (C.schemeTensor U) (C.directImage U)
      (((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj ((C.restrict U).obj F)).obj
        ((C.weights U).line.obj v))
      (((CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U)).obj ((C.restrict U).obj H)).obj
        ((C.weights U).line.obj w))) ≫
  (directImageToModules I D j U (C.localRoot U) (C.projection U) (C.directImage U) (C.dictionary U)).map
    (rootTensorRearrangement I D j G R TG C S U F H v w).hom

def tensorComponent (F H : QCoh R.stack) (U : X.Etale) (v w : Weight (B.obj.obj (op U))) :
    moduleTensor U.left (((P.functor.obj F).localObject U).functor.obj v)
      (((P.functor.obj H).localObject U).functor.obj w) ⟶
    ((P.functor.obj (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H)).localObject U).functor.obj
      (weightProduct v w) :=
  tensorMap (((P.localIso U).hom.app F).app v) (((P.localIso U).hom.app H).app w) ≫
    localTensorComponent I D j G R TG C S U F H v w ≫
      ((P.localIso U).inv.app (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H)).app (weightProduct v w)

/-- The bilinear certificate fixes all of its maps to the preceding
native direct-image/root-section recipe. Its coherence is construction output. -/
structure TensorBilinearity where
  bilinear : ∀ F H : QCoh R.stack, Bilinear G j (P.functor.obj F) (P.functor.obj H)
    (P.functor.obj (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H))
  normalized : ∀ (F H : QCoh R.stack) (U : X.Etale) (v w : Weight (B.obj.obj (op U))),
    (bilinear F H).map U v w = tensorComponent I D j G R TG C P S F H U v w

def tensorComparison (T : ParabolicBilinearTensorModels.TensorModel G j)
    (B : TensorBilinearity I D j G R TG C P S) (F H : QCoh R.stack) :
    (T.functor.obj (P.functor.obj F)).obj (P.functor.obj H) ⟶
      P.functor.obj (((CartesianStackTensorProducts.tensor R.stack TG).obj F).obj H) :=
  T.lift (B.bilinear F H)

end MathlibExt.AlgebraicGeometry.ParabolicRootComparisonMaps
