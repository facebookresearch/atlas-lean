/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import MathlibExt.AlgebraicGeometry.GeometricallyIntegral

open CategoryTheory AlgebraicGeometry

universe u

/-- An arbitrary integral scheme over an algebraically closed field is geometrically integral,
without any finite-type hypothesis. -/
example {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] : GeometricallyIntegral f :=
  GeometricallyIntegral.of_isIntegral_of_isAlgClosed f

/-- The affine line over `ℂ` is geometrically integral over `ℂ`. -/
example :
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))) :
        (Spec (CommRingCat.of (Polynomial ℂ)) ⟶ Spec (CommRingCat.of ℂ))) :=
  GeometricallyIntegral.of_isIntegral_of_isAlgClosed _
