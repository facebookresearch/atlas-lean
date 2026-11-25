/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootSourceModels

/-!
# The original log arrow in characteristic and DF coordinates

The characteristic inverse image is fixed on every native generator by
the original log-monoid map and its entire characteristic comparison.
The DF line comparison is fixed in every actual log-lift frame through
the native sheaf pullback, its unit and the original DF comparison.
This specifies zero-section cases as well as nonzero alpha values.

Source: Borne--Vistoli1001.0466v2 Proposition3.9; Talpo--Vistoli1410.1164v2 Sections3--5.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootMorphismModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams SmallEtaleGeometry
open DenominatorRootFamilies DenominatorRootStacks EtaleMonoidInverseImage
open DeligneFaltingsInverseImages LogRootSourceModels KatoChartCoefficientModels

variable [InverseImageTheory.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y)
  (CX : LogDFDictionary X D) (CY : LogDFDictionary Y D)

-- Specializing native DF generators requires a large dependent conversion.
set_option maxHeartbeats 2000000 in
/-- The actual source/target characteristic and line maps on every etale generator. -/
structure DFImage where
  characteristic : (monoidPullback f.map).obj CY.characteristic ⟶ CX.characteristic
  line : ComparisonAlong characteristic
    ((I X.scheme Y.scheme f.map CY.characteristic).object CY.df).pulled CX.df
  log_generators : ∀ (U : Y.scheme.Etale) (a : CY.characteristic.obj.obj (op U))
      (m : LogLift Y CY.characteristic CY.comparison U a),
    (CX.comparison.hom.app (op ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))).hom
      (ULift.up (characteristic.hom.app (op ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
        (generator f.map CY.characteristic U a))) =
    (LogStructures.characteristicMap X.scheme.smallEtaleTopology X.log).hom.app
      (op ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
        (f.logMap.left.hom.app (op U) m.val)
  frame_normalization : ∀ (U : Y.scheme.Etale) (a : CY.characteristic.obj.obj (op U))
      (m : LogLift Y CY.characteristic CY.comparison U a)
      (n : LogLift X CX.characteristic CX.comparison ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
        (characteristic.hom.app (op ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
          (generator f.map CY.characteristic U a))),
    n.val = f.logMap.left.hom.app (op U) m.val →
      (((I X.scheme Y.scheme f.map CY.characteristic).object CY.df).comparison U a).hom ≫
        (line.comparison ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
          (generator f.map CY.characteristic U a)).hom ≫
        (CX.frames.frame ((SmallEtaleGeometry.etaleBaseChange f.map).obj U)
          (characteristic.hom.app (op ((SmallEtaleGeometry.etaleBaseChange f.map).obj U))
            (generator f.map CY.characteristic U a)) n).hom =
      (Scheme.Modules.pullback (SmallEtaleGeometry.projection f.map U)).map (CY.frames.frame U a m).hom ≫
        SheafOfModules.pullbackObjUnitToUnit (SmallEtaleGeometry.projection f.map U).toRingCatSheafHom

end MathlibExt.AlgebraicGeometry.LogRootMorphismModels
