/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootParabolicPeriodModels
public import MathlibExt.AlgebraicGeometry.RootEtaleRestrictions

/-!
# Global parabolic objects from the actual weighted direct image

The local stack is the literal native restriction of the original root
pseudofunctor. Coefficients use its computed cartesian-module restriction.
Every local value, labelled weight arrow and coefficient arrow of Phi is
therefore the native pi_*(F tensor Lambda_v). Global assembly lands in the
existing actual Parabolic category, whose étale pullback, group periods,
sections and identity/composition diagrams are retained.

Period maps are normalized by the actual root-line base comparison and
the native adjunction projection-formula sequence, with all affine
coefficient generators fixed in the preceding dictionary types.

Source: Borne–Vistoli arXiv:1001.0466v2, Definition5.8 and Theorem6.1.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GlobalParabolicRootModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.CartesianStackModules _root_.AlgebraicGeometry.CartesianStackTensorProducts
open _root_.AlgebraicGeometry.SchemeStackModuleModels
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage
open ParabolicSheafCategories RootWeightEvaluations UniversalRootWeightLines
open RootStackProjectionModules RootWeightTensorModels RootParabolicPeriodModels
open SchemeStackTensorDictionaries ParabolicBilinearTensorModels

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (R : DenominatorRootStacks.Model I D j (𝟙 X))

/-- All data are selected together on the same literal root restrictions.
Generic dictionary producers are source integration, independently of
the Borne–Vistoli equivalence proof. -/
structure EtaleRootData where
  isStack : ∀ U : X.Etale,
    (RootEtaleRestrictions.pseudofunctor U.hom R.stack).IsStack (Scheme.fppfTopology.over U.left)
  localRoot : ∀ U : X.Etale, DenominatorRootStacks.Model I D j U.hom
  stack_eq : ∀ U : X.Etale,
    (localRoot U).stack = @RootEtaleRestrictions.stack X U.left U.hom R.stack (isStack U)
  scheme : ∀ U : X.Etale, SchemeStackModuleModels.Model (Over.mk (𝟙 U.left))
  projection : ∀ U : X.Etale, RootStackProjectionModules.Projection I D j U (localRoot U) (scheme U)
  directImage : ∀ U : X.Etale, DirectImage (projection U).morphism
  dictionary : ∀ U : X.Etale, ModuleDictionary (scheme U)
  tensor : ∀ U : X.Etale, TensorLanding (localRoot U).stack
  schemeTensor : ∀ U : X.Etale, TensorLanding (scheme U).stack
  tensorDictionary : ∀ U : X.Etale, TensorDictionary (scheme U) (dictionary U) (schemeTensor U)
  weights : ∀ U : X.Etale, StackWeights I D j U (localRoot U)
  weightTensor : ∀ U : X.Etale, WeightTensor I D j U (localRoot U) (weights U) (tensor U)
  baseLift : ∀ U : X.Etale, BaseLift I D j G U (localRoot U) (weights U)
  periods : ∀ U : X.Etale, PeriodData I D j G U (localRoot U) (weights U) (tensor U)
    (projection U) (directImage U) (dictionary U) (schemeTensor U) (baseLift U)

namespace EtaleRootData

variable {I D j G R} (C : EtaleRootData I D j G R)

def restrict (U : X.Etale) : QCoh R.stack ⥤ QCoh (C.localRoot U).stack := by
  letI : (RootEtaleRestrictions.pseudofunctor U.hom R.stack).IsStack
      (Scheme.fppfTopology.over U.left) := C.isStack U
  rw [C.stack_eq U]
  exact @RootEtaleRestrictions.restriction X U.left U.hom R.stack (C.isStack U)

/-- Universe adapter of RootStackProjectionModules.weightedDirectImage
at #2782 head22007ad969dd657172fd2a94eef155b7f7979827. Its original
signature fixes W in Type1, while the actual group-weight carrier B(U)
is in Type0. The body uses the same native tensor/direct-image functors. -/
def smallWeighted {W : Type} [Category.{0} W] (U : X.Etale)
    (L : W ⥤ QCoh (C.localRoot U).stack) : QCoh (C.localRoot U).stack ⥤ W ⥤ U.left.Modules :=
  CartesianStackTensorProducts.tensor (C.localRoot U).stack (C.tensor U) ⋙
    (Functor.whiskeringLeft W (QCoh (C.localRoot U).stack) (QCoh (C.localRoot U).stack)).obj L ⋙
    (Functor.whiskeringRight W (QCoh (C.localRoot U).stack) U.left.Modules).obj
      (directImageToModules I D j U (C.localRoot U) (C.projection U) (C.directImage U) (C.dictionary U))

/-- Literal local Phi, including its actual coefficient and weight maps. -/
def localPhi (U : X.Etale) : QCoh R.stack ⥤ Weight (B.obj.obj (op U)) ⥤ U.left.Modules :=
  C.restrict U ⋙ C.smallWeighted U (C.weights U).line

end EtaleRootData

def localForget (U : X.Etale) : Parabolic G j ⥤ Weight (B.obj.obj (op U)) ⥤ U.left.Modules where
  obj E := (E.localObject U).functor
  map a := (a.localMap U).map
  map_id _ := rfl
  map_comp _ _ := rfl

variable (C : EtaleRootData I D j G R)

/-- Source construction output in the actual global parabolic category.
The natural isomorphism fixes every object, labelled weight arrow and
coefficient map; the period equation fixes the source PF comparison. -/
structure PhiAssembly where
  functor : QCoh R.stack ⥤ Parabolic G j
  localIso : ∀ U : X.Etale, functor ⋙ localForget (D := D) (j := j) (G := G) U ≅ C.localPhi U
  period : ∀ (U : X.Etale) (F : QCoh R.stack)
    (p : Groupification (A.obj.obj (op U))) (w : Weight (B.obj.obj (op U))),
    ((localIso U).hom.app F).app (shift (j.hom.app (op U)).hom p w) ≫
      (PeriodData.recipe (DK := C.tensorDictionary U) (WT := C.weightTensor U) (C.periods U)
        ((C.restrict U).obj F) p w).hom =
    (((functor.obj F).localObject U).periodic p w).hom ≫
      LineBundleTaskContracts.tensorMap (𝟙 ((G.chart U).line p)) (((localIso U).hom.app F).app w)

end MathlibExt.AlgebraicGeometry.GlobalParabolicRootModels
