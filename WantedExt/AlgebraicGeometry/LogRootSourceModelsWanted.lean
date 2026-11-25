/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogRootSourceModels

/-!
# Source-normalized log/DF and infinite-root assembly

Each line is fixed by the original log-lift/frame torsor and all alpha,
unit, tensor and restriction maps. The infinite stack uses the existing
finite denominator roots and their actual compatible-root category.
No topos equivalence, preservation or reconstruction conclusion is an input.
Sources: Borne--Vistoli1001.0466v2 Proposition3.9; Talpo--Vistoli1410.1164v2 Sections2--4.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogRootSourceModels

open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks
open KatoChartCoefficientModels LogRootSourceModels

public def_wanted nativeLogDFDictionary [InverseImageTheory.{0}]
    (D : RegularSectionComparisons) (X : LogScheme.{0}) (hX : X.IsFineSaturated) :
    LogDFDictionary X D

public def_wanted nativeLogRootRealization [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) : RootRealization X D I

end WantedExt.AlgebraicGeometry.LogRootSourceModels
