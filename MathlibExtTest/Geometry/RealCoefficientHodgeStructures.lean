/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.RealCoefficientHodgeStructures

@[expose] public section

/-!
# Tests for real-coefficient Hodge structures

The Hodge–Riemann condition of a polarization says that the Hodge–Riemann
value of a nonzero vector of type `(p, q)` is a positive real number, not merely
a complex number with positive real part.
-/

noncomputable section

open MathlibExt.Geometry.RealCoefficientHodgeStructures

namespace MathlibExtTest.Geometry.RealCoefficientHodgeStructures

variable (A : Subfield ℝ) (V : ModuleCat.{0} A) (C : Conjugation A V) (w : ℤ)
  (H : PureHodgeStructure A V C w)

/-- The Hodge–Riemann value of a nonzero vector of type `(p, q)` is a positive
real number. -/
example (P : PurePolarization A V C w H) (p q : ℤ) (hpq : p + q = w)
    (v : complexCarrier A V) (hv : v ∈ H.F p ⊓ (H.F q).map C.map.toLinearMap) (hv0 : v ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      Complex.I ^ (p - q) * (-1 : ℂ) ^ (w * (w - 1) / 2) * P.complexForm v (C.map v) = r := by
  obtain ⟨him, hre⟩ := P.hodgeRiemann p q hpq v hv hv0
  exact ⟨_, hre, Complex.ext (by simp) (by simp [him])⟩

/-- The tensor value of `z` and `v` is conjugated to that of `z̄` and `v`. -/
example (z : ℂ) (v : V) : C.map (tensorValue A V z v) = tensorValue A V (star z) v :=
  C.tensor_normalization z v

end MathlibExtTest.Geometry.RealCoefficientHodgeStructures
