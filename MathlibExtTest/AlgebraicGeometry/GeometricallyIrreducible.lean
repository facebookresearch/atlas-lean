/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import MathlibExt.Algebra.TensorProduct.Domain
public import MathlibExt.AlgebraicGeometry.GeometricallyIrreducible

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

/-- Tensor product of a field with a polynomial ring over `ℂ` is a domain. -/
example : IsDomain (ℂ ⊗[ℂ] Polynomial ℂ) :=
  Algebra.TensorProduct.isDomain_of_isAlgClosed_of_field ℂ (Polynomial ℂ)

/-- Tensor product of two polynomial rings over `ℂ` is a domain. -/
example : IsDomain (Polynomial ℂ ⊗[ℂ] Polynomial ℂ) :=
  Algebra.TensorProduct.isDomain_of_isAlgClosed_of_finiteType (Polynomial ℂ) (Polynomial ℂ)

/-- The affine line over `ℂ` is geometrically irreducible over `ℂ`. -/
example :
    GeometricallyIrreducible
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (Polynomial ℂ))) :
        (Spec (CommRingCat.of (Polynomial ℂ)) ⟶ Spec (CommRingCat.of ℂ))) :=
  AlgebraicGeometry.GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed _
