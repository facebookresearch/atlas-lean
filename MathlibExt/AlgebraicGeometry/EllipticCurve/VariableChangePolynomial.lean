/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination

/-!
# The Weierstrass polynomial and its partial derivatives under a variable change

Let `W` be a Weierstrass curve over a field `F` and let `C = (u, r, s, t)` be a variable change.
Substituting `x = u² x' + r` and `y = u³ y' + u² s x' + t` into the Weierstrass polynomial
`f_W = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆` gives `u⁶ f_{C • W}(x', y')`
(`WeierstrassCurve.Affine.evalEval_polynomial_variableChange`), and its partial derivatives
`P_W = 2y + a₁ x + a₃` and `Q_W = 3x² + 2a₂ x + a₄ - a₁ y` become `u³ P_{C • W}` and
`u⁴ Q_{C • W} + s u³ P_{C • W}` (`WeierstrassCurve.Affine.evalEval_partials_variableChange`).
When the discriminant of `W` is nonzero, `P_W` and `Q_W` generate the unit ideal of the affine
coordinate ring `F[x, y] / (f_W)`
(`WeierstrassCurve.Affine.CoordinateRing.exists_mul_add_mul_eq_one_of_Δ_ne_zero`).

In Mathlib, `f_W` is `WeierstrassCurve.Affine.polynomial`, `P_W` is
`WeierstrassCurve.Affine.polynomialY` and `Q_W` is `-WeierstrassCurve.Affine.polynomialX`, all in
`F[X][Y]`, whose inner variable is `x'` (`Polynomial.C Polynomial.X`) and whose outer variable is
`y'` (`Polynomial.X`). The substitution evaluates the polynomial of the curve `W` mapped to
`F[X][Y]` at the two substituted coordinates.

## References

* J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
  <https://jmilne.org/math/Books/EC2.pdf>: Chapter II, Theorem 2.4, p. 52.
-/

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F]

namespace Affine

private lemma u_mul_a₁ (W : WeierstrassCurve F) (C : VariableChange F) :
    (C.u : F) * (C • W).a₁ = W.a₁ + 2 * C.s := by
  rw [variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]

private lemma u_mul_a₂ (W : WeierstrassCurve F) (C : VariableChange F) :
    (C.u : F) ^ 2 * (C • W).a₂ = W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2 := by
  rw [variableChange_a₂, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

private lemma u_mul_a₃ (W : WeierstrassCurve F) (C : VariableChange F) :
    (C.u : F) ^ 3 * (C • W).a₃ = W.a₃ + C.r * W.a₁ + 2 * C.t := by
  rw [variableChange_a₃, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

private lemma u_mul_a₄ (W : WeierstrassCurve F) (C : VariableChange F) :
    (C.u : F) ^ 4 * (C • W).a₄ = W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ -
      (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t := by
  rw [variableChange_a₄, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

private lemma u_mul_a₆ (W : WeierstrassCurve F) (C : VariableChange F) :
    (C.u : F) ^ 6 * (C • W).a₆ = W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3 -
      C.t * W.a₃ - C.t ^ 2 - C.r * C.t * W.a₁ := by
  rw [variableChange_a₆, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

/-- Maps an identity of `F` to the bivariate polynomial ring `F[X][Y]` by constants. -/
private lemma CC_congr {a b : F} (h : a = b) : (CC a : F[X][Y]) = CC b := by rw [h]

/-- **The Weierstrass polynomial after a variable change.** Let `F` be a field, let `W` be a
Weierstrass curve over `F` with coefficients `a₁, a₂, a₃, a₄, a₆`, and let
`f_W(x, y) = y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆`. Let `C = (u, r, s, t)` be a variable
change, with `u ∈ Fˣ` and `r, s, t ∈ F`, and let `W' = C • W`. Then, in the polynomial ring
`F[x', y']`, `f_W(u² x' + r, u³ y' + u² s x' + t) = u⁶ f_{W'}(x', y')`.

Here `F[x', y']` is `F[X][Y]` with inner variable `x'` and outer variable `y'`, `f_W` is
`WeierstrassCurve.Affine.polynomial`, and the left side evaluates the polynomial of `W` mapped to
`F[X][Y]` by constants at `u² x' + r` and `u³ y' + u² s x' + t`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52: the isomorphism
`(x : y : z) ↦ (u² x + r z : u³ y + s u² x + t z : z)` between the curves of the two equations,
with the coefficients of `W'`; the identity follows by expansion. -/
theorem evalEval_polynomial_variableChange (W : WeierstrassCurve F) (C : VariableChange F) :
    (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval
        (CC ((C.u : F) ^ 2) * Polynomial.C Polynomial.X + CC C.r)
        (CC ((C.u : F) ^ 3) * Y + CC ((C.u : F) ^ 2 * C.s) * Polynomial.C Polynomial.X + CC C.t) =
      CC ((C.u : F) ^ 6) * (C • W).toAffine.polynomial := by
  have h₁ := CC_congr (u_mul_a₁ W C)
  have h₂ := CC_congr (u_mul_a₂ W C)
  have h₃ := CC_congr (u_mul_a₃ W C)
  have h₄ := CC_congr (u_mul_a₄ W C)
  have h₆ := CC_congr (u_mul_a₆ W C)
  simp only [CC, map_mul, map_add, map_sub, map_pow, map_ofNat] at h₁ h₂ h₃ h₄ h₆
  rw [evalEval_polynomial, Affine.polynomial]
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingHom.coe_comp, Function.comp_apply,
    CC, map_mul, map_add, map_pow]
  linear_combination (-(CC (C.u : F) ^ 5) * Polynomial.C Polynomial.X * Y) * h₁ +
    (CC (C.u : F) ^ 4 * Polynomial.C Polynomial.X ^ 2) * h₂ +
    (-(CC (C.u : F) ^ 3) * Y) * h₃ + (CC (C.u : F) ^ 2 * Polynomial.C Polynomial.X) * h₄ + h₆

/-- **The partial derivatives of the Weierstrass polynomial after a variable change.** Let `F` be
a field, let `W` be a Weierstrass curve over `F` with coefficients `a₁, a₂, a₃, a₄, a₆`, and write
`P_W(x, y) = 2y + a₁ x + a₃` and `Q_W(x, y) = 3x² + 2a₂ x + a₄ - a₁ y` in `F[x, y]`. Let
`C = (u, r, s, t)` be a variable change, with `u ∈ Fˣ` and `r, s, t ∈ F`, and let `W' = C • W`.
Then, in `F[x', y']`, with `x = u² x' + r` and `y = u³ y' + u² s x' + t`,
`P_W(x, y) = u³ P_{W'}(x', y')` and `Q_W(x, y) = u⁴ Q_{W'}(x', y') + s u³ P_{W'}(x', y')`.

Here `F[x', y']` is `F[X][Y]` with inner variable `x'` and outer variable `y'`, `P_W` is
`WeierstrassCurve.Affine.polynomialY`, `Q_W` is `-WeierstrassCurve.Affine.polynomialX`, and the
left sides evaluate the polynomials of `W` mapped to `F[X][Y]` by constants at `x` and `y`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(b), p. 52, for the variable
change and the coefficients of `W'`; the identities follow by expansion. -/
theorem evalEval_partials_variableChange (W : WeierstrassCurve F) (C : VariableChange F) :
    (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomialY.evalEval
        (CC ((C.u : F) ^ 2) * Polynomial.C Polynomial.X + CC C.r)
        (CC ((C.u : F) ^ 3) * Y + CC ((C.u : F) ^ 2 * C.s) * Polynomial.C Polynomial.X + CC C.t) =
      CC ((C.u : F) ^ 3) * (C • W).toAffine.polynomialY ∧
    (-(W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomialX).evalEval
        (CC ((C.u : F) ^ 2) * Polynomial.C Polynomial.X + CC C.r)
        (CC ((C.u : F) ^ 3) * Y + CC ((C.u : F) ^ 2 * C.s) * Polynomial.C Polynomial.X + CC C.t) =
      CC ((C.u : F) ^ 4) * -(C • W).toAffine.polynomialX +
        CC (C.s * (C.u : F) ^ 3) * (C • W).toAffine.polynomialY := by
  have h₁ := CC_congr (u_mul_a₁ W C)
  have h₂ := CC_congr (u_mul_a₂ W C)
  have h₃ := CC_congr (u_mul_a₃ W C)
  have h₄ := CC_congr (u_mul_a₄ W C)
  simp only [CC, map_mul, map_add, map_sub, map_pow, map_ofNat] at h₁ h₂ h₃ h₄
  constructor
  · rw [evalEval_polynomialY, Affine.polynomialY]
    simp only [map_a₁, map_a₃, RingHom.coe_comp, Function.comp_apply,
      CC, map_mul, map_add, map_pow, map_ofNat]
    linear_combination (-(CC (C.u : F) ^ 2) * Polynomial.C Polynomial.X) * h₁ - h₃
  · rw [evalEval_neg, evalEval_polynomialX, Affine.polynomialX, Affine.polynomialY]
    simp only [map_a₁, map_a₂, map_a₄, RingHom.coe_comp, Function.comp_apply,
      CC, map_mul, map_add, map_pow, map_ofNat]
    linear_combination (CC (C.u : F) ^ 3 * Y - CC C.s * CC (C.u : F) ^ 2 *
        Polynomial.C Polynomial.X) * h₁ -
      (2 * CC (C.u : F) ^ 2 * Polynomial.C Polynomial.X) * h₂ - CC C.s * h₃ - h₄

/-- A ring homomorphism out of `F[X][Y]` sends the Weierstrass polynomial of `W` to the
Weierstrass polynomial of `W` mapped along the constants, evaluated at the images of the two
variables. -/
private lemma map_polynomial_eq_evalEval {L : Type*} [CommRing L] (W : WeierstrassCurve F)
    (φ : F[X][Y] →+* L) :
    φ W.toAffine.polynomial =
      (W.map (φ.comp (Polynomial.C.comp Polynomial.C))).toAffine.polynomial.evalEval
        (φ (Polynomial.C Polynomial.X)) (φ Y) := by
  rw [evalEval_polynomial, Affine.polynomial]
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, RingHom.coe_comp, Function.comp_apply,
    map_mul, map_add, map_sub, map_pow]
  ring

private lemma map_polynomialX_eq_evalEval {L : Type*} [CommRing L] (W : WeierstrassCurve F)
    (φ : F[X][Y] →+* L) :
    φ W.toAffine.polynomialX =
      (W.map (φ.comp (Polynomial.C.comp Polynomial.C))).toAffine.polynomialX.evalEval
        (φ (Polynomial.C Polynomial.X)) (φ Y) := by
  rw [evalEval_polynomialX, Affine.polynomialX]
  simp only [map_a₁, map_a₂, map_a₄, RingHom.coe_comp, Function.comp_apply,
    map_mul, map_add, map_sub, map_pow, map_ofNat]

private lemma map_polynomialY_eq_evalEval {L : Type*} [CommRing L] (W : WeierstrassCurve F)
    (φ : F[X][Y] →+* L) :
    φ W.toAffine.polynomialY =
      (W.map (φ.comp (Polynomial.C.comp Polynomial.C))).toAffine.polynomialY.evalEval
        (φ (Polynomial.C Polynomial.X)) (φ Y) := by
  rw [evalEval_polynomialY, Affine.polynomialY]
  simp only [map_a₁, map_a₃, RingHom.coe_comp, Function.comp_apply,
    map_mul, map_add, map_ofNat]
  ring

namespace CoordinateRing

/-- **The partial derivatives of a nonsingular Weierstrass polynomial generate the unit ideal.**
Let `F` be a field and let `W` be a Weierstrass curve over `F` with coefficients
`a₁, a₂, a₃, a₄, a₆` and discriminant `Δ_W ≠ 0`. Let
`A_W = F[x, y] / (y² + a₁ x y + a₃ y - x³ - a₂ x² - a₄ x - a₆)` be its affine coordinate ring.
Then the classes of `P_W = 2y + a₁ x + a₃` and `Q_W = 3x² + 2a₂ x + a₄ - a₁ y` generate the unit
ideal of `A_W`: there are `p, q ∈ A_W` with `p P_W + q Q_W = 1`.

Here `A_W` is `WeierstrassCurve.Affine.CoordinateRing`, `P_W` is
`WeierstrassCurve.Affine.polynomialY` and `Q_W` is `-WeierstrassCurve.Affine.polynomialX`.

Source: J. S. Milne, *Elliptic Curves*, second edition, World Scientific, 2021, author's version
<https://jmilne.org/math/Books/EC2.pdf>, Chapter II, Theorem 2.4(a), p. 52: the curve of a
Weierstrass equation is nonsingular if and only if `Δ ≠ 0`. The algebraic form is proved here: a
maximal ideal containing both classes would give a singular point of `W` over its residue
field. -/
theorem exists_mul_add_mul_eq_one_of_Δ_ne_zero (W : WeierstrassCurve F) (hΔ : W.Δ ≠ 0) :
    ∃ p q : W.toAffine.CoordinateRing,
      p * AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialY +
        q * AdjoinRoot.mk W.toAffine.polynomial (-W.toAffine.polynomialX) = 1 := by
  rw [← Ideal.mem_span_pair, ← Ideal.eq_top_iff_one]
  by_contra hJ
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hJ
  have hP : AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialY ∈ M :=
    hJM (Ideal.subset_span (Set.mem_insert _ _))
  have hQ : AdjoinRoot.mk W.toAffine.polynomial W.toAffine.polynomialX ∈ M := by
    have h := hJM (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton
      (AdjoinRoot.mk W.toAffine.polynomial (-W.toAffine.polynomialX)))))
    rwa [map_neg, neg_mem_iff] at h
  let φ : F[X][Y] →+* W.toAffine.CoordinateRing ⧸ M :=
    (Ideal.Quotient.mk M).comp (AdjoinRoot.mk W.toAffine.polynomial)
  let ι : F →+* W.toAffine.CoordinateRing ⧸ M := φ.comp (Polynomial.C.comp Polynomial.C)
  have hι : Function.Injective ι := ι.injective
  have hΔ' : (W.map ι).Δ ≠ 0 := by
    rw [map_Δ]
    exact (map_ne_zero_iff ι hι).mpr hΔ
  have hEq : (W.map ι).toAffine.Equation (φ (Polynomial.C Polynomial.X)) (φ Y) := by
    rw [Affine.Equation, ← map_polynomial_eq_evalEval]
    simp [φ, AdjoinRoot.mk_self]
  have hns := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ').mp hEq
  rcases hns.2 with hX | hY
  · apply hX
    rw [← map_polynomialX_eq_evalEval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hQ
  · apply hY
    rw [← map_polynomialY_eq_evalEval]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hP

end CoordinateRing

end Affine

end WeierstrassCurve
