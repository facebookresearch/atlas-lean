/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.XYIdeal

open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing

/-- Smoke test of `XYIdeal_ne_bot`. -/
example {R : Type*} [CommRing R] [Nontrivial R] {W : Affine R} (x : R) (y : R[X]) :
    XYIdeal W x y ≠ ⊥ :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal_ne_bot x y

/-- Consumer with the original binders for the coordinate criterion. -/
theorem exactSource {F : Type*} [Field F] {W : Affine F} {x₁ y₁ : F}
    (h : W.Equation x₁ y₁) (x₂ y₂ : F) :
    XYIdeal W x₁ (C y₁) = XYIdeal W x₂ (C y₂) ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  WeierstrassCurve.Affine.CoordinateRing.XYIdeal_eq_XYIdeal_iff h x₂ y₂

/-- Distinct points on the curve give distinct ideals: the second
coordinate is recovered from the ideal. -/
example {F : Type*} [Field F] {W : Affine F} {x y₁ y₂ : F}
    (h : W.Equation x y₁) (hxy : y₁ ≠ y₂) :
    XYIdeal W x (C y₁) ≠ XYIdeal W x (C y₂) := fun he =>
  hxy ((exactSource h x y₂).mp he).2
