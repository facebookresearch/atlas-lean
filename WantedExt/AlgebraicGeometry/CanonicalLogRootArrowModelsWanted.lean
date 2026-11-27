/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CanonicalLogRootArrowModels

/-!
# Root preservation of canonical infinite log-root arrows

All characteristic, frame, root-line, section, coefficient, family and
global finite-projection maps are fixed by the original log arrow.
Preserving every whole-fibre infinite root is a theorem conclusion,
not a field assumed by the canonical arrow construction.
Constructing the canonical finite and infinite arrows is left to a separate
development: it needs root realizations whose evaluated root comparisons are
coherent over the whole tower (identities, composites, base change and the
mixed base/exponent squares), which the realizations here do not record.
Source: Talpo--Vistoli1410.1164v2, Sections3--5 and Theorem5.24.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CanonicalLogRootArrowModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open EtaleLogSchemes EtaleLogDiagrams DenominatorRootStacks FiniteRootTowers
open KatoChartCoefficientModels LogRootSourceModels CanonicalLogRootArrowModels
open InfiniteRootPreservationModels InfiniteRootSectionModels

public theorem_wanted nativeLogRootPreservation [InverseImageTheory.{0}]
    (I : NativeDFImages.{0}) (D : RegularSectionComparisons)
    (X Y : LogScheme.{0}) (hX : X.IsFineSaturated) (hY : Y.IsFineSaturated)
    (f : EtaleLogSchemes.Hom X Y) (RX : RootRealization X D I) (RY : RootRealization Y D I)
    [HasBaseChanges RY.infinite.stack] [∀ n : Exponent, HasBaseChanges (RY.finite n).stack]
    (F : FiniteArrow I D f RX RY) (A : InfiniteArrow I D f RX RY F)
    [HasBaseChanges RX.infinite.stack]
    [HasBaseChanges (baseChanged RY.infinite.stack f.map)]
    (B : ∀ (T : Scheme.{0}) (b : T ⟶ X.scheme), BaseChangedMap A.morphism b)
    (TY : ∀ (T : Scheme.{0}) (b : T ⟶ X.scheme),
      HasTensorLanding (baseChanged (baseChanged RY.infinite.stack f.map) b)) :
    IsRootPreserving A.morphism B TY

end WantedExt.AlgebraicGeometry.CanonicalLogRootArrowModels
