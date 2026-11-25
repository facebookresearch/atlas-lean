/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.KummerFlatSiteComparisonModels

/-!
# Local Kummer-flat/root-fppf site comparison and native equivalence

Local object refinements, arrow lifting and local equality are source
construction outputs. Sheaf restriction, native inverse image and its
actual unit/counit are already fixed; equivalence is a separate theorem.
No global inverse chart functor or source equivalence is an input.
Source: Talpo--Vistoli1410.1164v2, Theorem6.16.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.KummerFlatSiteComparisonModels

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams EtaleLogNativeCategory
open DenominatorRootStacks FiniteRootTowers KatoChartCoefficientModels LogRootSourceModels
open InfiniteRootPreservationModels RepresentableStackFppfSites
open CanonicalKummerFlatSiteModels KummerFlatSiteComparisonModels

public theorem_wanted nativeRootSiteLocalRefinements [InverseImageTheory.{0}]
    [N : NativeCategoryModel.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) (RX : RootRealization X D I)
    [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
    (S : NativeSiteCategory RX.infinite.stack) (F : FunctorModel I D X RX S) :
    LocalRefinements I D X RX S F

public theorem_wanted nativeRootSiteContinuity [InverseImageTheory.{0}]
    [N : NativeCategoryModel.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) (RX : RootRealization X D I)
    [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
    (S : NativeSiteCategory RX.infinite.stack) (F : FunctorModel I D X RX S) :
    IsContinuous I D X RX S F

public theorem_wanted nativeRootSiteCocontinuity [InverseImageTheory.{0}]
    [N : NativeCategoryModel.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) (RX : RootRealization X D I)
    [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
    (S : NativeSiteCategory RX.infinite.stack) (F : FunctorModel I D X RX S) :
    IsCocontinuous I D X RX S F

public theorem_wanted nativeKummerFlatSheafEquivalence [InverseImageTheory.{0}]
    [N : NativeCategoryModel.{0}] (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X : LogScheme.{0}) (hX : X.IsFineSaturated) (RX : RootRealization X D I)
    [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
    (S : NativeSiteCategory RX.infinite.stack) (F : FunctorModel I D X RX S)
    (L : LocalRefinements I D X RX S F)
    (h : IsContinuous I D X RX S F)
    (hc : IsCocontinuous I D X RX S F)
    [HasSheafify (sourceTopology D X) (Type 2)]
    (adjoint : letI := S.category
      (sheafPushforward I D X RX S F (A := Type 2) h).IsRightAdjoint) :
    letI := S.category
    (sheafPushforward I D X RX S F (A := Type 2) h).IsEquivalence

end WantedExt.AlgebraicGeometry.KummerFlatSiteComparisonModels
