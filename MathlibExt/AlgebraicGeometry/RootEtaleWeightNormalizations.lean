/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ParabolicRootEtaleMaps
public import MathlibExt.AlgebraicGeometry.RootNativeFamilyComparisons

/-!
# All coefficient normalization of the universal weight restriction

The parameter-base arrow is computed from native Over.map and its
literal equality. Root-family arrows lie in the actual DF-extension
groupoid. Positive root-line comparison is the preceding actual
inverse-image/root-arrow/identity-etale recipe on every coefficient.
Unit and tensor normalization in WeightRestriction then retain all
group weights. Nonzero values of a section are not used to determine
the line comparison.

Source: Borne–Vistoli arXiv:1001.0466v2, Sections4.3/6.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RootEtaleWeightNormalizations

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackFibreModels _root_.AlgebraicGeometry.StackAffineModules
open _root_.AlgebraicGeometry.CartesianStackModules
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage
open ParabolicSheafCategories UniversalRootWeightLines RootWeightEvaluations GlobalParabolicRootModels
open ParabolicRootEtaleMaps ModuleTensorPullbackSections

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (R : DenominatorRootStacks.Model I D j (𝟙 X))
  (C : EtaleRootData I D j G R) (S : LocalStackModels I D j G R C)

def coefficientIdentity {U V : X.Etale} (f : V ⟶ U) (T : Over V.left) :
    (Over.map V.hom).obj T ⟶ (Over.map U.hom).obj ((Over.map f.left).obj T) :=
  Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ ((T.hom ≫ f.left) ≫ U.hom) = T.hom ≫ V.hom
    simp only [Category.id_comp, Category.assoc, MorphismProperty.Over.w f])

theorem positiveWeight_eq {U V : X.Etale} (f : V ⟶ U) (b : B.obj.obj (op U)) :
    (weightMap ((B.obj.map f.op).hom)).obj (positiveWeight U b) =
      positiveWeight V ((B.obj.map f.op).hom b) :=
  Weight.ext (groupMap_of ((B.obj.map f.op).hom) b)

def coefficientArrow {U V : X.Etale} (f : V ⟶ U) (a : AffinePoint (C.localRoot V).stack) :
    (Over.map V.hom).obj a.obj.base ⟶ (Over.map U.hom).obj ((S.view f).obj a).obj.base :=
  coefficientIdentity f a.obj.base ≫ eqToHom (congrArg (Over.map U.hom).obj
    (@StackProjectionBaseChange.affineView_base U.left V.left f.left (C.localRoot U).stack
      (S.isStack f) (C.localRoot V).stack (S.stack_eq f) a).symm)

def restrictedValue {U V : X.Etale} (f : V ⟶ U) (M : QCoh (C.localRoot U).stack)
    (a : AffinePoint (C.localRoot V).stack) (x : ((S.restriction f).obj M).obj.obj (op a)) :
    M.obj.obj (op ((S.view f).obj a)) :=
  @StackProjectionBaseChange.restrictionValue U.left V.left f.left (C.localRoot U).stack
    (S.isStack f) (C.localRoot V).stack (S.stack_eq f) M a x

structure FamilyMaps where
  reindexing : ∀ {U V : X.Etale} (f : V ⟶ U) (a : AffinePoint (C.localRoot V).stack),
    RootReindexing I D j (coefficientArrow I D j G R C S f a)
  rootMap : ∀ {U V : X.Etale} (f : V ⟶ U) (a : AffinePoint (C.localRoot V).stack),
    rootObject I D j V (C.localRoot V) a ⟶
      (reindexing f a).functor.obj (rootObject I D j U (C.localRoot U) ((S.view f).obj a))
  generators : ∀ {U V : X.Etale} (f : V ⟶ U) (a : AffinePoint (C.localRoot V).stack)
      (b : B.obj.obj (op U)),
    RootNativeFamilyComparisons.GeneratorNormalization (B := B)
      (coefficientArrow I D j G R C S f a)
      (localGenerators B U ((S.view f).obj a).obj.base b)
      (localGenerators B V a.obj.base ((B.obj.map f.op).hom b))

variable (F : FamilyMaps I D j G R C S)

def positiveSource {U V : X.Etale} (f : V ⟶ U) (b : B.obj.obj (op U))
    (a : AffinePoint (C.localRoot V).stack)
    (x : ((S.restriction f).obj ((C.weights U).line.obj (positiveWeight U b))).obj.obj (op a)) :
    Γ(((rootObject I D j U (C.localRoot U) ((S.view f).obj a)).of.extended.chart
      (identityEtale ((S.view f).obj a).obj.base.left)).module
        (localGenerators B U ((S.view f).obj a).obj.base b),⊤) :=
  ((positiveIso I D j U (C.localRoot U) ((S.view f).obj a)
      ((C.weights U).groupified ((S.view f).obj a)) ((C.weights U).laws ((S.view f).obj a)) b).hom.val.app
        (op (⊤ : ((S.view f).obj a).obj.base.left.Opens))).hom
    ((C.weights U).sections (positiveWeight U b) ((S.view f).obj a)
      (restrictedValue I D j G R C S f ((C.weights U).line.obj (positiveWeight U b)) a x))

def positiveTarget {U V : X.Etale} (f : V ⟶ U) (b : B.obj.obj (op U))
    (a : AffinePoint (C.localRoot V).stack)
    (y : ((C.weights V).line.obj (positiveWeight V ((B.obj.map f.op).hom b))).obj.obj (op a)) :
    Γ(((rootObject I D j V (C.localRoot V) a).of.extended.chart
      (identityEtale a.obj.base.left)).module (localGenerators B V a.obj.base ((B.obj.map f.op).hom b)),⊤) :=
  ((positiveIso I D j V (C.localRoot V) a ((C.weights V).groupified a) ((C.weights V).laws a)
      ((B.obj.map f.op).hom b)).hom.val.app (op (⊤ : a.obj.base.left.Opens))).hom
    ((C.weights V).sections (positiveWeight V ((B.obj.map f.op).hom b)) a y)

def positiveRecipe {U V : X.Etale} (f : V ⟶ U) (b : B.obj.obj (op U))
    (a : AffinePoint (C.localRoot V).stack)
    (x : ((S.restriction f).obj ((C.weights U).line.obj (positiveWeight U b))).obj.obj (op a)) :
    Γ(((rootObject I D j V (C.localRoot V) a).of.extended.chart
      (identityEtale a.obj.base.left)).module (localGenerators B V a.obj.base ((B.obj.map f.op).hom b)),⊤) :=
  ((RootNativeFamilyComparisons.comparison I D j (coefficientArrow I D j G R C S f a)
      (F.reindexing f a) (rootObject I D j U (C.localRoot U) ((S.view f).obj a))
      (rootObject I D j V (C.localRoot V) a) (F.rootMap f a)
      (localGenerators B U ((S.view f).obj a).obj.base b)
      (localGenerators B V a.obj.base ((B.obj.map f.op).hom b)) (F.generators f a b)).hom.val.app
        (op (⊤ : a.obj.base.left.Opens))).hom
    (localPullbackOn (coefficientArrow I D j G R C S f a).left
      (((rootObject I D j U (C.localRoot U) ((S.view f).obj a)).of.extended.chart
        (identityEtale ((S.view f).obj a).obj.base.left)).module
          (localGenerators B U ((S.view f).obj a).obj.base b)) ⊤ ⊤ (by simp)
      (positiveSource I D j G R C S f b a x))

structure WeightFamilyNormalization (N : RestrictionNormalization I D j G R C S)
    (W : WeightRestriction I D j G R C S N) : Prop where
  positive : ∀ {U V : X.Etale} (f : V ⟶ U) (b : B.obj.obj (op U))
      (a : AffinePoint (C.localRoot V).stack)
      (x : ((S.restriction f).obj ((C.weights U).line.obj (positiveWeight U b))).obj.obj (op a)),
    positiveTarget I D j G R C f b a
      ((eqToHom (congrArg (C.weights V).line.obj (positiveWeight_eq (B := B) f b))).hom.app (op a)
        (((W.comparison f).hom.app (positiveWeight U b)).hom.app (op a) x)) =
      positiveRecipe I D j G R C S F f b a x

end MathlibExt.AlgebraicGeometry.RootEtaleWeightNormalizations
