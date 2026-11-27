/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.EllipticCurve.AffineInvariantDifferential

open MvPolynomial KaehlerDifferential

namespace WeierstrassCurve

-- The invariant differential of any Weierstrass curve with `Δ ≠ 0` over a field.
example {F : Type} [Field F] (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    W.mvMk W.mvPolynomialP • W.invariantDifferential hΔ = D F _ (W.mvMk (X 0)) ∧
      W.mvMk W.mvPolynomialQ • W.invariantDifferential hΔ = D F _ (W.mvMk (X 1)) :=
  (W.invariantDifferential_spec hΔ).1

-- `y² = x³ - x` over `ℚ`, with `Δ = 64`.
def curve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

theorem curve_Δ : curve.Δ = 64 := by
  simp [curve, Δ, b₂, b₄, b₆, b₈]
  norm_num

theorem curve_Δ_ne_zero : curve.Δ ≠ 0 := by
  rw [curve_Δ]
  norm_num

-- Its differentials are free of rank one over `ℚ[x, y] / (y² - x³ + x)`.
example : ∃ b : Module.Basis (Fin 1) curve.MvCoordinateRing
    (KaehlerDifferential ℚ curve.MvCoordinateRing),
      b 0 = curve.invariantDifferential curve_Δ_ne_zero :=
  (curve.invariantDifferential_spec curve_Δ_ne_zero).2.2

-- `P = 2y` and `Q = 3x² - 1` generate the unit ideal of `ℚ[x, y] / (y² - x³ + x)`.
example : ∃ p q : curve.MvCoordinateRing,
    p * curve.mvMk curve.mvPolynomialP + q * curve.mvMk curve.mvPolynomialQ = 1 :=
  curve.exists_mul_add_mul_eq_one_of_Δ_ne_zero curve_Δ_ne_zero

-- The scaling `x = 4x'`, `y = 8y'` (`u = 2`): the pushforward of `ω` is `ω' / 2`.
example : kaehlerMapAlgHom (curve.variableChangeEquiv ⟨Units.mk0 2 two_ne_zero, 0, 0, 0⟩).toAlgHom
      (curve.invariantDifferential curve_Δ_ne_zero) =
    (((Units.mk0 (2 : ℚ) two_ne_zero)⁻¹ : ℚˣ) : ℚ) •
      ((⟨Units.mk0 2 two_ne_zero, 0, 0, 0⟩ : VariableChange ℚ) • curve).invariantDifferential
        (curve.variableChange_Δ_ne_zero _ curve_Δ_ne_zero) :=
  (curve.invariantDifferential_variableChange _ curve_Δ_ne_zero).2

-- A general variable change.
example {F : Type} [Field F] (W : WeierstrassCurve F) (C : VariableChange F) (hΔ : W.Δ ≠ 0)
    (g : MvPolynomial (Fin 2) F) :
    W.variableChangeEquiv C (W.mvMk g) = (C • W).mvMk (variableChangeSubst C g) :=
  (W.invariantDifferential_variableChange C hΔ).1 g

end WeierstrassCurve
