/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogRootMorphismModels

/-!
# Source-normalized log/DF arrow assembly

Every characteristic generator and line-frame comparison is fixed by
the original log arrow and native scheme inverse image. Root preservation,
the topos comparison and reconstruction remain separate theorem outputs.
Sources: Borne--Vistoli1001.0466v2 Proposition3.9; Talpo--Vistoli1410.1164v2 Sections3--5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogRootMorphismModels

open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks
open LogRootSourceModels LogRootMorphismModels KatoChartCoefficientModels

public def_wanted nativeLogDFImage [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y : LogScheme.{0}) (hX : X.IsFineSaturated) (hY : Y.IsFineSaturated)
    (f : EtaleLogSchemes.Hom X Y) (CX : LogDFDictionary X D) (CY : LogDFDictionary Y D) :
    DFImage I D f CX CY

end WantedExt.AlgebraicGeometry.LogRootMorphismModels
