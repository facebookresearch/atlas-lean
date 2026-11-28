/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePolynomial

/-!
# Two Weierstrass relations on the same coordinate ring

Let `W` and `W'` be Weierstrass curves over a field `F` and let `x', y'` be the coordinate
functions of the affine coordinate ring `A_{W'} = F[x', y'] / (f_{W'})`. If, for units
`u₁, u₂ ∈ Fˣ` and `r, s', t ∈ F`, the elements `u₁ x' + r` and `u₂ y' + s' x' + t` satisfy the
Weierstrass equation of `W` in `A_{W'}`, then `u₂² = u₁³`, and with `u = u₂ / u₁` (so that
`u² = u₁`, `u³ = u₂`) and `s = s' / u²` the curve `W'` is `C • W` for the variable change
`C = (u, r, s, t)` (`WeierstrassCurve.Affine.CoordinateRing.eq_variableChange_of_equation`).

The proof compares polynomials in `F[x'][y']`: the substituted Weierstrass polynomial of `W` is
divisible by the monic quadratic `f_{W'}`, its difference with `u₂² f_{W'}` has degree at most `1`
in `y'` and so vanishes, and its `x'³` coefficient gives `u₂² = u₁³`; then the polynomial identity
`WeierstrassCurve.Affine.evalEval_polynomial_variableChange` identifies it with `u⁶ f_{C • W}`.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>: Chapter II, proof of Theorem 2.1(b), pp. 50–51, and
  Theorem 2.4(b) and its proof, pp. 52–53.
-/

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- **Evaluating a Weierstrass polynomial on the coordinate ring of another curve.** Let `F` be a
field and let `W`, `W'` be Weierstrass curves over `F`, with `A_{W'} = F[X][Y] / (f_{W'})`. For
`a, b ∈ F[X][Y]`, the Weierstrass polynomial of the base change of `W` to `A_{W'}`, evaluated at the
classes of `a` and `b`, is the class of the Weierstrass polynomial of `W` (mapped to `F[X][Y]` by
constants) evaluated at `a` and `b`. -/
theorem mk_evalEval_baseChange (W W' : WeierstrassCurve F) (a b : F[X][Y]) :
    (W.baseChange W'.toAffine.CoordinateRing).toAffine.polynomial.evalEval
      (Affine.CoordinateRing.mk W'.toAffine a) (Affine.CoordinateRing.mk W'.toAffine b) =
    Affine.CoordinateRing.mk W'.toAffine
      ((W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval a b) := by
  rw [Affine.evalEval_polynomial, Affine.evalEval_polynomial]
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, map_mul, map_add, map_sub,
    map_pow, RingHom.coe_comp, Function.comp_apply]
  rfl

/-- A Weierstrass curve is determined by its Weierstrass polynomial. -/
private lemma eq_of_polynomial_eq {W W' : WeierstrassCurve F}
    (h : W.toAffine.polynomial = W'.toAffine.polynomial) : W = W' := by
  have h1 := congrArg (fun p => p.coeff 1) h
  have h0 := congrArg (fun p => p.coeff 0) h
  simp only [Affine.polynomial, coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X_one,
    coeff_C, coeff_X_zero] at h1 h0
  norm_num at h1 h0
  have a1 : W.a₁ = W'.a₁ := by
    simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (fun p => p.coeff 1) h1
  have a3 : W.a₃ = W'.a₃ := by
    simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (fun p => p.coeff 0) h1
  have a2 : W.a₂ = W'.a₂ := by
    simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (fun p => p.coeff 2) h0
  have a4 : W.a₄ = W'.a₄ := by
    simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (fun p => p.coeff 1) h0
  have a6 : W.a₆ = W'.a₆ := by
    simpa [coeff_X, coeff_C, coeff_X_pow] using congrArg (fun p => p.coeff 0) h0
  exact WeierstrassCurve.ext a1 a2 a3 a4 a6

/-- The substituted Weierstrass polynomial of `W` is divisible by that of `W'` when the
substituted coordinates satisfy the equation of `W` in `A_{W'}`. -/
private lemma dvd_of_equation (W W' : WeierstrassCurve F) (u₁ u₂ r s' t : F)
    (h : (W.baseChange W'.toAffine.CoordinateRing).toAffine.Equation
      (algebraMap F _ u₁ * Affine.CoordinateRing.mk W'.toAffine (C X) + algebraMap F _ r)
      (algebraMap F _ u₂ * Affine.CoordinateRing.mk W'.toAffine Y +
        algebraMap F _ s' * Affine.CoordinateRing.mk W'.toAffine (C X) + algebraMap F _ t)) :
    W'.toAffine.polynomial ∣ (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval
      (CC u₁ * C X + CC r) (CC u₂ * Y + CC s' * C X + CC t) := by
  have hx : ∀ c : F, algebraMap F W'.toAffine.CoordinateRing c =
      Affine.CoordinateRing.mk W'.toAffine (CC c) := fun c => rfl
  have e₁ : algebraMap F _ u₁ * Affine.CoordinateRing.mk W'.toAffine (C X) + algebraMap F _ r =
      Affine.CoordinateRing.mk W'.toAffine (CC u₁ * C X + CC r) := by
    simp only [hx, map_mul, map_add]
  have e₂ : algebraMap F _ u₂ * Affine.CoordinateRing.mk W'.toAffine Y +
        algebraMap F _ s' * Affine.CoordinateRing.mk W'.toAffine (C X) + algebraMap F _ t =
      Affine.CoordinateRing.mk W'.toAffine (CC u₂ * Y + CC s' * C X + CC t) := by
    simp only [hx, map_mul, map_add]
  rwa [e₁, e₂, Affine.Equation, mk_evalEval_baseChange, Affine.CoordinateRing.mk,
    AdjoinRoot.mk_eq_zero] at h

/-- The `x'³` coefficient: if the substituted Weierstrass polynomial of `W` is divisible by that
of `W'`, then `u₂² = u₁³`. -/
private lemma sq_eq_cube_of_dvd (W W' : WeierstrassCurve F) (u₁ u₂ r s' t : F)
    (h : W'.toAffine.polynomial ∣
      (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval
        (CC u₁ * C X + CC r) (CC u₂ * Y + CC s' * C X + CC t)) :
    u₂ ^ 2 = u₁ ^ 3 := by
  set P := (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval
    (CC u₁ * C X + CC r) (CC u₂ * Y + CC s' * C X + CC t)
  have hD : P - CC (u₂ ^ 2) * W'.toAffine.polynomial =
      C (C (2 * u₂ * s' + W.a₁ * u₂ * u₁ - u₂ ^ 2 * W'.a₁) * X +
          C (2 * u₂ * t + W.a₁ * u₂ * r + W.a₃ * u₂ - u₂ ^ 2 * W'.a₃)) * Y +
        C (C (u₂ ^ 2 - u₁ ^ 3) * X ^ 3 +
          C (s' ^ 2 + W.a₁ * u₁ * s' - 3 * u₁ ^ 2 * r - W.a₂ * u₁ ^ 2 + u₂ ^ 2 * W'.a₂) * X ^ 2 +
          C (2 * s' * t + W.a₁ * (u₁ * t + r * s') + W.a₃ * s' - 3 * u₁ * r ^ 2 -
            2 * W.a₂ * u₁ * r - W.a₄ * u₁ + u₂ ^ 2 * W'.a₄) * X +
          C (t ^ 2 + W.a₁ * r * t + W.a₃ * t - r ^ 3 - W.a₂ * r ^ 2 - W.a₄ * r - W.a₆ +
            u₂ ^ 2 * W'.a₆)) := by
    simp only [P, CC, Affine.evalEval_polynomial, Affine.polynomial, map_a₁, map_a₂, map_a₃,
      map_a₄, map_a₆, RingHom.coe_comp, Function.comp_apply, map_mul, map_add, map_sub, map_pow,
      map_ofNat]
    ring
  have hdvd : W'.toAffine.polynomial ∣ P - CC (u₂ ^ 2) * W'.toAffine.polynomial :=
    dvd_sub h (dvd_mul_left _ _)
  have hzero : P - CC (u₂ ^ 2) * W'.toAffine.polynomial = 0 := by
    refine Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd ?_
    rw [Affine.natDegree_polynomial, hD]
    exact lt_of_le_of_lt Polynomial.natDegree_linear_le (by norm_num)
  rw [hD] at hzero
  have h0 := congrArg (fun p => p.coeff 0) hzero
  simp only [coeff_add, coeff_mul_X_zero, coeff_C_zero, zero_add, coeff_zero] at h0
  have h3 := congrArg (fun p => p.coeff 3) h0
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h3
  norm_num at h3
  linear_combination h3

namespace Affine.CoordinateRing

/-- **Comparing two Weierstrass relations on the same coordinate ring.** Let `F` be a field, let
`W` and `W'` be Weierstrass curves over `F`, and let `x', y'` be the coordinate functions in the
affine coordinate ring `A_{W'} = F[x', y'] / (f_{W'})` of `W'`. Let `u₁, u₂ ∈ Fˣ` and
`r, s', t ∈ F`, and suppose that `x̃ = u₁ x' + r` and `ỹ = u₂ y' + s' x' + t` satisfy the
Weierstrass equation of `W` in `A_{W'}`:
`ỹ² + a₁ x̃ ỹ + a₃ ỹ = x̃³ + a₂ x̃² + a₄ x̃ + a₆`.
Then `u₂² = u₁³`; the unit `u = u₂ / u₁` satisfies `u² = u₁` and `u³ = u₂`; and `W' = C • W` for
the variable change `C = (u, r, s, t)` with `s = s' / u² = s' / u₁`, so that `s' = s u²`.

Here `A_{W'}` is `WeierstrassCurve.Affine.CoordinateRing`, `x'` and `y'` are the classes of
`C X` and `Y`, the equation of `W` in `A_{W'}` is that of the base change of `W` to `A_{W'}`, and
`C • W` is Mathlib's action of `WeierstrassCurve.VariableChange` (`x = u² x' + r`,
`y = u³ y' + u² s x' + t`).

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, proof of Theorem 2.1(b), pp. 50–51 ("any
polynomial satisfied by `x', y'` is a multiple of `Y² - X³ - a' X - b'`, from which it follows that
`u₂² = u₁³`", in characteristic `≠ 2, 3`), and Theorem 2.4(b) and its proof, pp. 52–53, for
general Weierstrass equations over an arbitrary field. -/
theorem eq_variableChange_of_equation (W W' : WeierstrassCurve F) (u₁ u₂ : Fˣ) (r s' t : F)
    (h : (W.baseChange W'.toAffine.CoordinateRing).toAffine.Equation
      (algebraMap F _ (u₁ : F) * mk W'.toAffine (C X) + algebraMap F _ r)
      (algebraMap F _ (u₂ : F) * mk W'.toAffine Y +
        algebraMap F _ s' * mk W'.toAffine (C X) + algebraMap F _ t)) :
    (u₂ : F) ^ 2 = u₁ ^ 3 ∧ ((u₂ * u₁⁻¹ : Fˣ) : F) ^ 2 = u₁ ∧ ((u₂ * u₁⁻¹ : Fˣ) : F) ^ 3 = u₂ ∧
      W' = (⟨u₂ * u₁⁻¹, r, s' / u₁, t⟩ : VariableChange F) • W := by
  have hdvd := dvd_of_equation W W' _ _ r s' t h
  have hsq := sq_eq_cube_of_dvd W W' _ _ r s' t hdvd
  have hu₁ : (u₁ : F) ≠ 0 := u₁.ne_zero
  set C : VariableChange F := ⟨u₂ * u₁⁻¹, r, s' / u₁, t⟩ with hC
  have hu2 : (C.u : F) ^ 2 = u₁ := by
    simp only [hC, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hsq
  have hu3 : (C.u : F) ^ 3 = u₂ := by
    have : (C.u : F) ^ 3 = (C.u : F) ^ 2 * C.u := by ring
    rw [this, hu2]
    simp only [hC, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hs : (u₁ : F) * C.s = s' := by
    simp only [hC]
    field_simp
  refine ⟨hsq, hu2, hu3, ?_⟩
  have key := Affine.evalEval_polynomial_variableChange W C
  rw [hu2, hu3, hs] at key
  have hr : C.r = r := rfl
  have ht : C.t = t := rfl
  rw [hr, ht] at key
  rw [key] at hdvd
  have hunit : IsUnit (CC ((C.u : F) ^ 6) : F[X][Y]) :=
    (isUnit_C.mpr (isUnit_C.mpr ((C.u.isUnit).pow 6)))
  have hdvd' : W'.toAffine.polynomial ∣ (C • W).toAffine.polynomial :=
    (hunit.dvd_mul_left).mp hdvd
  refine (eq_of_polynomial_eq ?_).symm
  exact eq_of_monic_of_dvd_of_natDegree_le Affine.monic_polynomial Affine.monic_polynomial hdvd'
    (by rw [Affine.natDegree_polynomial, Affine.natDegree_polynomial])

end Affine.CoordinateRing

end WeierstrassCurve
