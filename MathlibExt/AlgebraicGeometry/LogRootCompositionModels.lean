/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CanonicalLogRootArrowModels

/-!
# Original logarithmic commuting squares and root comparison cells

The source square commutes on every actual log section, before alpha.
Its DF images and finite-root comparison cells retain all original line
frames and coefficient maps. The root cell is required to induce exactly
those comparisons; it cannot be an unrelated triangle over the base.

Source: Talpo--Vistoli1410.1164v2, Theorem5.24 and Section6.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.LogRootCompositionModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite _root_.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels CanonicalLogRootArrowModels
open LogRootMorphismModels GeometricFiniteRootArrowModels

variable [InverseImageTheory.{0}]
  (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
  {X Y Z : LogScheme.{0}} (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z)
  (h : EtaleLogSchemes.Hom X Z)
  (CX : LogDFDictionary X D) (CY : LogDFDictionary Y D) (CZ : LogDFDictionary Z D)
  (F : DFImage I D f CX CY) (G : DFImage I D g CY CZ) (H : DFImage I D h CX CZ)

/-- The original composite square uses the native log-section formula. -/
structure OriginalSquare where
  base : f.map ≫ g.map = h.map
  log_sections : ∀ (U : Z.scheme.Etale)
      (m : (LogStructures.monoid Z.scheme.smallEtaleTopology Z.log).obj.obj (op U)),
    h.logMap.left.hom.app (op U) m =
      (LogStructures.monoid X.scheme.smallEtaleTopology X.log).obj.map
        ((EtaleBaseChangeCoherence.composition f.map g.map ≪≫
          eqToIso (congrArg SmallEtaleGeometry.etaleBaseChange base)).inv.app U).op
        (f.logMap.left.hom.app (op ((SmallEtaleGeometry.etaleBaseChange g.map).obj U))
          (g.logMap.left.hom.app (op U) m))

/-- The original pulled line map, before choosing any root comparison cell. -/
def lineMap (a : EtaleLogSchemes.Hom X Z)
    (CX : LogDFDictionary X D) (CZ : LogDFDictionary Z D)
    (H : DFImage I D a CX CZ) (U : Z.scheme.Etale) (v : CZ.characteristic.obj.obj (op U)) :=
  (((I X.scheme Z.scheme a.map CZ.characteristic).object CZ.df).comparison U v).hom ≫
    (H.line.comparison ((SmallEtaleGeometry.etaleBaseChange a.map).obj U)
      (EtaleMonoidInverseImage.generator a.map CZ.characteristic U v)).hom

end MathlibExt.AlgebraicGeometry.LogRootCompositionModels
