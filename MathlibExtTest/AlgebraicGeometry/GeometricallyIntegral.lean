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

/-- The affine line over `ℂ` is geometrically integral over `ℂ`. -/
example :
    GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))) :
        (Spec (CommRingCat.of (Polynomial ℂ)) ⟶ Spec (CommRingCat.of ℂ))) := by
  haveI : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ)))) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed _
