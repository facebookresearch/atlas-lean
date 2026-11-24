/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.GeometricFiniteRootArrowModels

/-!
# Native original-parameter finite-root comparison assembly

All characteristic generators and full line comparisons use the actual
iterated/direct inverse images, original log arrow and native DF maps.
The global root/site and preservation/reconstruction conclusions remain separate.
Source: Talpo--Vistoli1410.1164v2, Sections3--5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.GeometricFiniteRootArrowModels

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks
open LogRootSourceModels LogRootMorphismModels KatoChartCoefficientModels
open GeometricFiniteRootArrowModels

public def_wanted nativeParameterRootImage [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y : LogScheme.{0}) (f : EtaleLogSchemes.Hom X Y)
    (CX : LogDFDictionary X D) (CY : LogDFDictionary Y D) (F : DFImage I D f CX CY)
    (T : Over X.scheme) : ParameterImage I D f CX CY F T

end WantedExt.AlgebraicGeometry.GeometricFiniteRootArrowModels
