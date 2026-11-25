/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogRootSiteImageModels
public import MathlibExt.AlgebraicGeometry.NativeKummerFlatModels

/-!
# The canonical Kummer-flat root image and its actual fppf fibres

The image map is fixed by the original root-family Grothendieck functor
and its native base-change view. Representability, flatness and local
finite presentation concern that same map on every scheme test fibre.
Source: Talpo--Vistoli1410.1164v2, Proposition6.14.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogRootSiteImageModels

open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels CanonicalLogRootArrowModels
open RelativeStackImageModels InfiniteRootPreservationModels LogRootSiteImageModels
open NativeKummerFlatModels

public def_wanted nativeLogRootImage [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y : LogScheme.{0}) (hX : X.IsFineSaturated) (hY : Y.IsFineSaturated)
    (f : EtaleLogSchemes.Hom X Y) (RX : RootRealization X D I) (RY : RootRealization Y D I)
    [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]
    (F : FiniteArrow I D f RX RY) (A : InfiniteArrow I D f RX RY F)
    (V : ImageModel f.map RX.infinite.stack) : ImageArrow I D f RX RY F A V

public theorem_wanted nativeKummerFlatRootImage [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y : LogScheme.{0}) (f : EtaleLogSchemes.Hom X Y) (hf : IsKummerFlat D f)
    (RX : RootRealization X D I) (RY : RootRealization Y D I)
    [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]
    (F : FiniteArrow I D f RX RY) (A : InfiniteArrow I D f RX RY F)
    (V : ImageModel f.map RX.infinite.stack) (B : ImageArrow I D f RX RY F A V) :
    FppfImage I D f RX RY F A V B

end WantedExt.AlgebraicGeometry.LogRootSiteImageModels
