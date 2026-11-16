/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CanonicalKummerFlatSiteModels

/-!
# Canonical Kummer-flat site functor assembly

The target fixes each source log object's actual root-family category,
its image over the base, original finite root maps and all total-category
arrow comparisons. It assumes no inverse chart functor or topos equivalence.
Source: Talpo--Vistoli1410.1164v2, Proposition6.14 and Theorem6.16.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CanonicalKummerFlatSiteModels

open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams EtaleLogNativeCategory
open DenominatorRootStacks FiniteRootTowers KatoChartCoefficientModels LogRootSourceModels
open InfiniteRootPreservationModels RepresentableStackFppfSites CanonicalKummerFlatSiteModels

public def_wanted nativeCanonicalKummerFlatFunctor [InverseImageTheory.{0}]
    [N : NativeCategoryModel.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) (RX : RootRealization X D I)
    [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
    (S : NativeSiteCategory RX.infinite.stack) : FunctorModel I D X RX S

end WantedExt.AlgebraicGeometry.CanonicalKummerFlatSiteModels
