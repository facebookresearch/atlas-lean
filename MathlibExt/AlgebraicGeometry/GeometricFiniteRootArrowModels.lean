/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FiniteLogRootArrowModels
public import MathlibExt.AlgebraicGeometry.InfiniteRootPreservationModels

/-!
# Finite root maps on every original parameter scheme

The source DF image is pulled through the original parameter map.
Every monoid image is fixed by the native adjunction generators and
composition comparison. Every line comparison is fixed by the native
inverse-image source and original DF frame comparison. Restricting a
root along this actual comparison defines its finite target root.

Source: Talpo--Vistoli1410.1164v2, Sections3--5 and Theorem5.24.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.GeometricFiniteRootArrowModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootFamilies DenominatorRootStacks
open DeligneFaltingsSheaves DeligneFaltingsInverseImages EtaleMonoidInverseImage
open FiniteRootTowers LogRootSourceModels LogRootMorphismModels KatoChartCoefficientModels

variable [InverseImageTheory.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
  (CX : LogDFDictionary X D) (CY : LogDFDictionary Y D) (F : DFImage I D f CX CY)

abbrev sourceMonoid (T : Over X.scheme) := (monoidPullback T.hom).obj CX.characteristic

abbrev targetBase (T : Over X.scheme) := (Over.map f.map).obj T

abbrev targetMonoid (T : Over X.scheme) :=
  (monoidPullback (targetBase f T).hom).obj CY.characteristic

abbrev sourceDF (T : Over X.scheme) := pulledStructure I CX.df T

abbrev targetDF (T : Over X.scheme) := pulledStructure I CY.df (targetBase f T)

abbrev iteratedMonoid (T : Over X.scheme) :=
  (monoidPullback T.hom).obj ((monoidPullback f.map).obj CY.characteristic)

abbrev iteratedDF (T : Over X.scheme) :=
  ((I T.left X.scheme T.hom ((monoidPullback f.map).obj CY.characteristic)).object
    ((I X.scheme Y.scheme f.map CY.characteristic).object CY.df).pulled).pulled

def directMonoidComparison (T : Over X.scheme) :
    iteratedMonoid D f CY T ≅ targetMonoid D f CY T :=
  (EtaleMonoidCoherence.composition T.hom f.map).app CY.characteristic

/-- The same original DF arrow in each actual parameter family. -/
structure ParameterImage (T : Over X.scheme) where
  characteristic : targetMonoid D f CY T ⟶ sourceMonoid D CX T
  comparison : ComparisonAlong characteristic (targetDF I D f CY T) (sourceDF I D CX T)
  direct : ComparisonAlong (directMonoidComparison D f CY T).hom
    (iteratedDF I D f CY T) (targetDF I D f CY T)
  projection : ∀ U : Y.scheme.Etale,
    SmallEtaleGeometry.projection T.hom ((SmallEtaleGeometry.etaleBaseChange f.map).obj U) ≫
      SmallEtaleGeometry.projection f.map U =
    ((EtaleBaseChangeCoherence.composition T.hom f.map).hom.app U).left ≫
      SmallEtaleGeometry.projection (T.hom ≫ f.map) U
  direct_generator : ∀ (U : Y.scheme.Etale) (a : CY.characteristic.obj.obj (op U)),
    (directMonoidComparison D f CY T).hom.hom.app
      (op ((SmallEtaleGeometry.etaleBaseChange T.hom).obj
        ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)))
      (generator T.hom ((monoidPullback f.map).obj CY.characteristic)
        ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
        (generator f.map CY.characteristic U a)) =
    (targetMonoid D f CY T).obj.map
      ((EtaleBaseChangeCoherence.composition T.hom f.map).hom.app U).op
      (generator (T.hom ≫ f.map) CY.characteristic U a)
  direct_normalization : ∀ (U : Y.scheme.Etale) (a : CY.characteristic.obj.obj (op U)),
    (Scheme.Modules.pullback
      (SmallEtaleGeometry.projection T.hom ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))).map
      (((I X.scheme Y.scheme f.map CY.characteristic).object CY.df).comparison U a).hom ≫
    (((I T.left X.scheme T.hom ((monoidPullback f.map).obj CY.characteristic)).object
      ((I X.scheme Y.scheme f.map CY.characteristic).object CY.df).pulled).comparison
        ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
        (generator f.map CY.characteristic U a)).hom ≫
    (direct.comparison
      ((SmallEtaleGeometry.etaleBaseChange T.hom).obj
        ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
      (generator T.hom ((monoidPullback f.map).obj CY.characteristic)
        ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
        (generator f.map CY.characteristic U a))).hom =
    (Scheme.Modules.pullbackComp
      (SmallEtaleGeometry.projection T.hom ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
      (SmallEtaleGeometry.projection f.map U)).hom.app ((CY.df.chart U).module a) ≫
      eqToHom (congrArg (fun h => (Scheme.Modules.pullback h).obj ((CY.df.chart U).module a))
        (projection U)) ≫
      (Scheme.Modules.pullbackComp
        ((EtaleBaseChangeCoherence.composition T.hom f.map).hom.app U).left
        (SmallEtaleGeometry.projection (T.hom ≫ f.map) U)).inv.app ((CY.df.chart U).module a) ≫
      (Scheme.Modules.pullback
        ((EtaleBaseChangeCoherence.composition T.hom f.map).hom.app U).left).map
        (((I T.left Y.scheme (T.hom ≫ f.map) CY.characteristic).object CY.df).comparison U a).hom ≫
      ((targetDF I D f CY T).reindex
        ((EtaleBaseChangeCoherence.composition T.hom f.map).hom.app U)
        (generator (T.hom ≫ f.map) CY.characteristic U a)).hom ≫
      eqToHom (congrArg
        ((targetDF I D f CY T).chart ((SmallEtaleGeometry.etaleBaseChange T.hom).obj
          ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))).module (direct_generator U a).symm)
  pulled : PullbackComparison I T.hom F.characteristic
    ((I X.scheme Y.scheme f.map CY.characteristic).object CY.df).pulled CX.df F.line
  monoid_square : (directMonoidComparison D f CY T).hom ≫ characteristic =
    (monoidPullback T.hom).map F.characteristic
  line_square : ∀ (U : T.left.Etale) (a : (iteratedMonoid D f CY T).obj.obj (op U)),
    (direct.comparison U a).hom ≫
      (comparison.comparison U ((directMonoidComparison D f CY T).hom.hom.app (op U) a)).hom ≫
        eqToHom (congrArg ((sourceDF I D CX T).chart U).module
          (ConcreteCategory.congr_hom (congrArg (fun h => h.hom.app (op U)) monoid_square) a)) =
    (pulled.comparison.comparison U a).hom
  generators : ∀ (U : Y.scheme.Etale) (a : CY.characteristic.obj.obj (op U)),
    characteristic.hom.app (op ((SmallEtaleGeometry.etaleBaseChange (targetBase f T).hom).obj U))
      (generator (targetBase f T).hom CY.characteristic U a) =
    (sourceMonoid D CX T).obj.map
      ((EtaleBaseChangeCoherence.composition T.hom f.map).inv.app U).op
      (generator T.hom CX.characteristic
        ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
        (F.characteristic.hom.app (op ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
          (generator f.map CY.characteristic U a)))

/-- Finite restriction on the actual parameter root groupoids. -/
def finiteFunctor (T : Over X.scheme) (P : ParameterImage I D f CX CY F T)
    (n : Exponent)
    (Q : FiniteLogRootArrowModels.Restriction (targetDF I D f CY T) (sourceDF I D CX T)
      P.characteristic P.comparison n) :
    FiniteLogRootArrowModels.FiniteFibre (sourceDF I D CX T) n ⥤
      FiniteLogRootArrowModels.FiniteFibre (targetDF I D f CY T) n := Q.functor

end MathlibExt.AlgebraicGeometry.GeometricFiniteRootArrowModels
