/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.LogRootInfiniteCompositionModels

/-!
# Original log-root composition through all finite line coefficients

The requested comparison uses the actual original log square, finite
root functors, original n-root lines, native parameter identity, and
all infinite projection maps. The topos equivalence is a separate goal.
Source: Talpo--Vistoli1410.1164v2, Theorem5.24 and Section6.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.LogRootCompositionModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels LogRootCompositionModels
open InfiniteRootPreservationModels CanonicalLogRootArrowModels LogRootInfiniteCompositionModels

public def_wanted nativeLogRootComposition [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y Z : LogScheme.{0}) (hX : X.IsFineSaturated) (hY : Y.IsFineSaturated)
    (hZ : Z.IsFineSaturated) (f : EtaleLogSchemes.Hom X Y) (g : EtaleLogSchemes.Hom Y Z)
    (h : EtaleLogSchemes.Hom X Z) (RX : RootRealization X D I)
    (RY : RootRealization Y D I) (RZ : RootRealization Z D I)
    [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]
    [HasBaseChanges RZ.infinite.stack] [∀ n : Exponent, HasBaseChanges (RZ.finite n).stack]
    (F : FiniteArrow I D f RX RY) (G : FiniteArrow I D g RY RZ) (H : FiniteArrow I D h RX RZ)
    (AF : InfiniteArrow I D f RX RY F) (AG : InfiniteArrow I D g RY RZ G)
    (AH : InfiniteArrow I D h RX RZ H) (S : OriginalSquare f g h) :
    InfiniteComposition I D f g h RX RY RZ F G H AF AG AH S

end WantedExt.AlgebraicGeometry.LogRootCompositionModelsWanted
