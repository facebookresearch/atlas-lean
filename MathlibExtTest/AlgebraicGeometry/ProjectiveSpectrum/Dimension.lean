/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.Dimension
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Tests for `MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.Dimension`. -/

@[expose] public section

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

#check @ProjectiveSpectrum.toPrimeSpectrum
#check @ProjectiveSpectrum.strictMono_toPrimeSpectrum
#check @ProjectiveSpectrum.exists_lt_toPrimeSpectrum
#check @ProjectiveSpectrum.length_add_one_le_ringKrullDim
#check @Proj.topologicalKrullDim_eq
#check @Proj.topologicalKrullDim_lt

/-- A point of `Proj` of the polynomial ring `ℚ[X, Y]` lies strictly below a prime of `ℚ[X, Y]`. -/
example (x : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ)) :
    ∃ q : PrimeSpectrum (MvPolynomial (Fin 2) ℚ),
      ProjectiveSpectrum.toPrimeSpectrum (MvPolynomial.homogeneousSubmodule (Fin 2) ℚ) x < q :=
  ProjectiveSpectrum.exists_lt_toPrimeSpectrum _ x
