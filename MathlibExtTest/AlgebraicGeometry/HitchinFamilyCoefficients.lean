/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HitchinFamilyCoefficients
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open CategoryTheory Opposite AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.GeometricHiggsFamilies
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

set_option backward.isDefEq.respectTransparency false

/-- Rank2 elementary coefficient1 has the trace sign, not minus trace. -/
example {X : Scheme} {L : X.Modules} (E : TwistedBundle X L 2)
    (K : CharacteristicSections E) {U : X.Opens} (F : AffineTwistedFrame E U) :
    (F.powerBasis 1).repr (((traceSection K).val.app (op U)).hom (1 : Γ(X,U))) () =
      (LinearMap.toMatrix F.basis F.basis (framedEnd E F)).trace := by
  rw [Matrix.trace_eq_neg_charpoly_coeff]
  simpa [traceSection, framedCharpoly] using K.local_normalization U F 1 (by decide)

/-- The rank2 constant elementary coefficient is the actual determinant. -/
example {X : Scheme} {L : X.Modules} (E : TwistedBundle X L 2)
    (K : CharacteristicSections E) {U : X.Opens} (F : AffineTwistedFrame E U) :
    (F.powerBasis 2).repr (((determinantSection K).val.app (op U)).hom (1 : Γ(X,U))) () =
      (LinearMap.toMatrix F.basis F.basis (framedEnd E F)).det := by
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simpa [determinantSection, framedCharpoly] using K.local_normalization U F 2 (by decide)
