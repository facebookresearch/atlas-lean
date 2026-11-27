/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ParabolicRootComparisonMaps
public import MathlibExt.AlgebraicGeometry.StackProjectionBaseChange

/-!
# Actual étale reindexing maps of the weighted root direct image

Root inverse image is literal native stack-module precomposition.
The structural comparisons are equalities of these fixed functors.
Base change is the native adjunction mate of the preceding pullback
square, normalized on all affine tests and all coefficient sections.
Weighted reindexing uses that map, the original universal weight-line
comparison, and actual root restriction/tensor identifications.

Source: Borne–Vistoli arXiv:1001.0466v2, Definition5.8, Section6
and Theorem6.1. Construction and coherence are Wanted outputs.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.ParabolicRootEtaleMaps

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackFibreModels _root_.AlgebraicGeometry.StackAffineModules
open _root_.AlgebraicGeometry.CartesianStackModules _root_.AlgebraicGeometry.CartesianStackTensorProducts
open _root_.AlgebraicGeometry.SchemeStackModuleModels
open DeligneFaltingsCategories DeligneFaltingsSheaves DenominatorRootStacks EtaleMonoidInverseImage
open ParabolicSheafCategories UniversalRootWeightLines GlobalParabolicRootModels
open ParabolicRootComparisonMaps ParabolicBilinearTensorModels

variable {X : Scheme.{0}}
  [∀ (Y Z : Scheme.{0}) (f : Y ⟶ Z), HasInverseImage f]
  (I : NativeDFImages.{0}) {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (j : A ⟶ B) (G : GroupifiedDF D)
  (R : DenominatorRootStacks.Model I D j (𝟙 X))
  (C : EtaleRootData I D j G R)

/-- Every local root object is the same literal base-changed
pseudofunctor, including its nonreduced parameter schemes and all arrows. -/
structure LocalStackModels where
  isStack : ∀ {U V : X.Etale} (f : V ⟶ U),
    (RootEtaleRestrictions.pseudofunctor f.left (C.localRoot U).stack).IsStack
      (Scheme.fppfTopology.over V.left)
  stack_eq : ∀ {U V : X.Etale} (f : V ⟶ U),
    (C.localRoot V).stack = @RootEtaleRestrictions.stack U.left V.left f.left
      (C.localRoot U).stack (isStack f)

namespace LocalStackModels

variable {I D j G R C} (S : LocalStackModels I D j G R C)

def restriction {U V : X.Etale} (f : V ⟶ U) :
    QCoh (C.localRoot U).stack ⥤ QCoh (C.localRoot V).stack :=
  @StackProjectionBaseChange.rootRestriction U.left V.left f.left (C.localRoot U).stack
    (S.isStack f) (C.localRoot V).stack (S.stack_eq f)

def view {U V : X.Etale} (f : V ⟶ U) :
    AffinePoint (C.localRoot V).stack ⥤ AffinePoint (C.localRoot U).stack :=
  @StackProjectionBaseChange.affineView U.left V.left f.left (C.localRoot U).stack
    (S.isStack f) (C.localRoot V).stack (S.stack_eq f)

end LocalStackModels

variable (S : LocalStackModels I D j G R C)

/-- All structural comparisons are of computed native operations. -/
structure RestrictionNormalization : Prop where
  global_eq : ∀ {U V : X.Etale} (f : V ⟶ U), C.restrict U ⋙ S.restriction f = C.restrict V
  tensor_eq : ∀ {U V : X.Etale} (f : V ⟶ U) (F H : QCoh (C.localRoot U).stack),
    (S.restriction f).obj (((tensor (C.localRoot U).stack (C.tensor U)).obj F).obj H) =
      ((tensor (C.localRoot V).stack (C.tensor V)).obj ((S.restriction f).obj F)).obj
        ((S.restriction f).obj H)
  unit_eq : ∀ {U V : X.Etale} (f : V ⟶ U),
    (S.restriction f).obj (structureModule (C.localRoot U).stack) = structureModule (C.localRoot V).stack

def LocalPullbackSquare {U V : X.Etale} (f : V ⟶ U)
    (H : StackProjectionBaseChange.SchemePullbackLanding f.left) : Type 1 :=
  @StackProjectionBaseChange.PullbackSquare U.left V.left f.left (C.localRoot U).stack
    (S.isStack f) (C.localRoot V).stack (S.stack_eq f)
      (C.scheme U) (C.scheme V) (C.projection U).morphism (C.projection V).morphism
        (C.dictionary U) (C.dictionary V) H
          (C.projection U).test_normalization (C.projection V).test_normalization

def baseChange {U V : X.Etale} (f : V ⟶ U)
    (H : StackProjectionBaseChange.SchemePullbackLanding f.left)
    (Q : LocalPullbackSquare I D j G R C S f H) (M : QCoh (C.localRoot U).stack) :
    (Scheme.Modules.pullback f.left).obj ((C.dictionary U).toModules.obj ((C.directImage U).functor.obj M)) ⟶
      (C.dictionary V).toModules.obj ((C.directImage V).functor.obj ((S.restriction f).obj M)) :=
  @StackProjectionBaseChange.moduleMap U.left V.left f.left (C.localRoot U).stack
    (S.isStack f) (C.localRoot V).stack (S.stack_eq f)
      (C.scheme U) (C.scheme V) (C.projection U).morphism (C.projection V).morphism
        (C.dictionary U) (C.dictionary V) H
          (C.projection U).test_normalization (C.projection V).test_normalization
            (C.directImage U) (C.directImage V) Q M

variable (N : RestrictionNormalization I D j G R C S)

structure WeightRestriction where
  comparison : ∀ {U V : X.Etale} (f : V ⟶ U),
    (C.weights U).line ⋙ S.restriction f ≅
      weightMap ((B.obj.map f.op).hom) ⋙ (C.weights V).line
  unit : ∀ {U V : X.Etale} (f : V ⟶ U),
    (S.restriction f).map (C.weightTensor U).unit.hom ≫ (comparison f).hom.app ⟨1⟩ ≫
        eqToHom (congrArg (C.weights V).line.obj
          (show (weightMap ((B.obj.map f.op).hom)).obj ⟨1⟩ = ⟨1⟩ from Weight.ext (map_one _))) =
      eqToHom (N.unit_eq f) ≫ (C.weightTensor V).unit.hom
  multiplication : ∀ {U V : X.Etale} (f : V ⟶ U)
      (v w : Weight (B.obj.obj (op U))),
    (S.restriction f).map ((C.weightTensor U).multiplication v w).hom ≫
      (comparison f).hom.app (weightProduct v w) =
    eqToHom (N.tensor_eq f ((C.weights U).line.obj v) ((C.weights U).line.obj w)) ≫
      (tensorUncurried (C.localRoot V).stack (C.tensor V)).map
        (X := ((S.restriction f).obj ((C.weights U).line.obj v),
          (S.restriction f).obj ((C.weights U).line.obj w)))
        (Y := ((C.weights V).line.obj ((weightMap ((B.obj.map f.op).hom)).obj v),
          (C.weights V).line.obj ((weightMap ((B.obj.map f.op).hom)).obj w)))
        ((comparison f).hom.app v, (comparison f).hom.app w) ≫
          ((C.weightTensor V).multiplication ((weightMap ((B.obj.map f.op).hom)).obj v)
            ((weightMap ((B.obj.map f.op).hom)).obj w)).hom ≫
              eqToHom (congrArg (C.weights V).line.obj
                (show weightProduct ((weightMap ((B.obj.map f.op).hom)).obj v)
                    ((weightMap ((B.obj.map f.op).hom)).obj w) =
                  (weightMap ((B.obj.map f.op).hom)).obj (weightProduct v w)
                  from Weight.ext (map_mul _ _ _).symm))

variable (W : WeightRestriction I D j G R C S N)

def weightedRootMap {U V : X.Etale} (f : V ⟶ U) (F : QCoh R.stack)
    (w : Weight (B.obj.obj (op U))) :
    (S.restriction f).obj (((tensor (C.localRoot U).stack (C.tensor U)).obj
      ((C.restrict U).obj F)).obj ((C.weights U).line.obj w)) ⟶
    ((tensor (C.localRoot V).stack (C.tensor V)).obj ((C.restrict V).obj F)).obj
      ((C.weights V).line.obj ((weightMap ((B.obj.map f.op).hom)).obj w)) :=
  eqToHom (N.tensor_eq f ((C.restrict U).obj F) ((C.weights U).line.obj w)) ≫
    (tensorUncurried (C.localRoot V).stack (C.tensor V)).map
      (eqToHom (congrArg (fun P ↦ P.obj F) (N.global_eq f)), (W.comparison f).hom.app w)

def reindexMap {U V : X.Etale} (f : V ⟶ U)
    (H : StackProjectionBaseChange.SchemePullbackLanding f.left)
    (Q : LocalPullbackSquare I D j G R C S f H) (F : QCoh R.stack)
    (w : Weight (B.obj.obj (op U))) :
    (Scheme.Modules.pullback f.left).obj (((C.localPhi U).obj F).obj w) ⟶
      ((C.localPhi V).obj F).obj ((weightMap ((B.obj.map f.op).hom)).obj w) :=
  baseChange I D j G R C S f H Q
      (((tensor (C.localRoot U).stack (C.tensor U)).obj ((C.restrict U).obj F)).obj ((C.weights U).line.obj w)) ≫
    ((C.directImage V).functor ⋙ (C.dictionary V).toModules).map
      (weightedRootMap I D j G R C S N W f F w)

structure PhiReindexNormalization
    (P : PhiAssembly I D j G R C)
    (H : ∀ {U V : X.Etale} (f : V ⟶ U), StackProjectionBaseChange.SchemePullbackLanding f.left)
    (Q : ∀ {U V : X.Etale} (f : V ⟶ U), LocalPullbackSquare I D j G R C S f (H f)) : Prop where
  reindex : ∀ {U V : X.Etale} (f : V ⟶ U) (F : QCoh R.stack)
      (w : Weight (B.obj.obj (op U))),
    (Scheme.Modules.pullback f.left).map (((P.localIso U).hom.app F).app w) ≫
      reindexMap I D j G R C S N W f (H f) (Q f) F w =
    (((P.functor.obj F).reindex f).hom.app w) ≫
      ((P.localIso V).hom.app F).app ((weightMap ((B.obj.map f.op).hom)).obj w)

end MathlibExt.AlgebraicGeometry.ParabolicRootEtaleMaps
