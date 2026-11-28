/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.IsIntegral
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Tests for `MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.IsIntegral`. -/

@[expose] public section

open AlgebraicGeometry

#check @ProjectiveSpectrum.botPoint
#check @ProjectiveSpectrum.botPoint_asHomogeneousIdeal
#check @ProjectiveSpectrum.closure_botPoint
#check @ProjectiveSpectrum.irreducibleSpace_of_isDomain
#check @Proj.isReduced_of_isReduced
#check @Proj.isIntegral_of_isDomain

attribute [local instance] MvPolynomial.gradedAlgebra in
/-- The projective plane over `ℚ`, as `Proj ℚ[X, Y, Z]`, is integral. -/
example : IsIntegral (Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ)) :=
  Proj.isIntegral_of_isDomain _ ⟨1, one_pos, MvPolynomial.X 0,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℚ 0),
    MvPolynomial.X_ne_zero 0⟩
