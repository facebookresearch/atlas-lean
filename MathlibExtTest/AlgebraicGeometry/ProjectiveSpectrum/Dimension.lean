/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.Dimension

/-! Tests for `MathlibExt.AlgebraicGeometry.ProjectiveSpectrum.Dimension`. -/

@[expose] public section

open AlgebraicGeometry

#check @ringKrullDim_le_of_isIntegral
#check @ProjectiveSpectrum.toPrimeSpectrum
#check @ProjectiveSpectrum.strictMono_toPrimeSpectrum
#check @ProjectiveSpectrum.exists_lt_toPrimeSpectrum
#check @ProjectiveSpectrum.length_add_one_le_ringKrullDim
#check @Proj.topologicalKrullDim_eq
#check @Proj.topologicalKrullDim_lt

/-- A quotient ring is integral over the ring, so its dimension is at most that of the ring. -/
example (A : Type) [CommRing A] (I : Ideal A) : ringKrullDim (A ⧸ I) ≤ ringKrullDim A :=
  ringKrullDim_le_of_isIntegral A (A ⧸ I)
