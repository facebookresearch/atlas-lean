/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.InfiniteRootReconstructionModels

/-!
# Unique native log recovery from universal-root-preserving morphisms

The actual scheme map is supplied. Preservation refers to every infinite
root on the entire geometric fibre, including nonreduced scheme tests.
The recovered native log arrow induces the given root arrow through its
original finite-root maps, up to an actual invertible modification.
Source: Talpo--Vistoli1410.1164v2, Theorem5.24.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.InfiniteRootReconstructionModels

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.StackCycleGeometry
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels InfiniteRootPreservationModels
open InfiniteRootSectionModels InfiniteRootReconstructionModels

public theorem_wanted nativeUniversalRootReconstruction [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y : LogScheme.{0}) (hX : X.IsFineSaturated) (hY : Y.IsFineSaturated)
    (RX : RootRealization X D I) (RY : RootRealization Y D I)
    [HasBaseChanges RX.infinite.stack] [∀ n : Exponent, HasBaseChanges (RX.finite n).stack]
    (f : Y.scheme ⟶ X.scheme)
    (q : StackHom RY.infinite.stack (baseChanged RX.infinite.stack f))
    [HasBaseChanges RY.infinite.stack] [HasBaseChanges (baseChanged RX.infinite.stack f)]
    (B : ∀ (T : Scheme.{0}) (b : T ⟶ Y.scheme), BaseChangedMap q b)
    (TY : ∀ (T : Scheme.{0}) (b : T ⟶ Y.scheme),
      HasTensorLanding (baseChanged (baseChanged RX.infinite.stack f) b))
    (hq : IsRootPreserving q B TY) :
    IsReconstruction I D X Y RX RY f q

end WantedExt.AlgebraicGeometry.InfiniteRootReconstructionModels
