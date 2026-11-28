/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Definitions/Def_WeierstrassCurve_LegendreModulus.lean`
`Definitions/Def_WeierstrassCurve_HasseInvariant.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import MathlibExt.AlgebraicGeometry.EllipticCurve.HasseInvariant

@[expose] public section

/-!
# Legendre modulus of a Weierstrass curve

For a Weierstrass curve `W` and abscissas `x₁` and `x₂`, this file defines `thirdTwoTorsionX`,
which is `-b₂/4 - x₁ - x₂`, the Legendre parameter `legendreLambda`, which is
`(x₃ - x₁) / (x₂ - x₁)` for `x₃ = thirdTwoTorsionX x₁ x₂`, and the variable change
`legendreVariableChange`. When `2 ≠ 0` and `x₁`, `x₂` are two roots of the 2-torsion polynomial
`4X³ + b₂X² + 2b₄X + b₆`, `x₃` is its third root, and `legendreVariableChange` completes the
square and moves `x₁` to `0`. In characteristic different from two, the Legendre curve
`y² = x(x - 1)(x - t)` has parameter `t` at the roots `0` and `1`, and the parameter is invariant
under change of variables; it is compatible with field homomorphisms in every characteristic.
-/

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- **Third root of the 2-torsion polynomial.** For a Weierstrass curve $W$ over a field and
$x_1, x_2$ in it, `W.thirdTwoTorsionX x₁ x₂` is $-b_2/4 - x_1 - x_2$. If $2 \ne 0$ and $x_1, x_2$
are two of the three roots, counted with multiplicity, of $4X^3 + b_2X^2 + 2b_4X + b_6$, it is the
remaining root, since the roots sum to $-b_2/4$. -/
def thirdTwoTorsionX (W : WeierstrassCurve F) (x₁ x₂ : F) : F := -W.b₂ / 4 - x₁ - x₂

/-- **Legendre parameter.** For a Weierstrass curve $W$ over a field and $x_1, x_2$ in it,
`W.legendreLambda x₁ x₂` is $(x_3 - x_1)/(x_2 - x_1)$, where $x_3$ is `W.thirdTwoTorsionX x₁ x₂`;
division by zero gives $0$, so the value is $0$ when $x_2 = x_1$. For the Legendre curve
$y^2 = x(x - 1)(x - t)$ with $x_1 = 0$ and $x_2 = 1$ it is $t$ when $2 \ne 0$
(`legendreLambda_legendreCurve`). -/
def legendreLambda (W : WeierstrassCurve F) (x₁ x₂ : F) : F :=
  (W.thirdTwoTorsionX x₁ x₂ - x₁) / (x₂ - x₁)

/-- **Variable change towards Legendre form.** For a Weierstrass curve $W$ over a field, $x_1$
and $w \ne 0$, `W.legendreVariableChange x₁ w hw` is the variable change
$(u, r, s, t) = (w, x_1, -a_1/2, -(a_3 + x_1a_1)/2)$, that is, $x = w^2x' + x_1$ and
$y = w^3y' - (a_1/2)w^2x' - (a_3 + x_1a_1)/2$. When $2 \ne 0$ it completes the square, so the new
curve has $a_1 = a_3 = 0$, and it moves $x = x_1$ to $x' = 0$. -/
def legendreVariableChange (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) : VariableChange F :=
  ⟨Units.mk0 w hw, x₁, -W.a₁ / 2, -(W.a₃ + x₁ * W.a₁) / 2⟩

@[simp] theorem legendreVariableChange_u (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    ((W.legendreVariableChange x₁ w hw).u : F) = w := rfl

@[simp] theorem legendreVariableChange_r (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).r = x₁ := rfl

@[simp] theorem legendreVariableChange_s (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).s = -W.a₁ / 2 := rfl

@[simp] theorem legendreVariableChange_t (W : WeierstrassCurve F) (x₁ w : F) (hw : w ≠ 0) :
    (W.legendreVariableChange x₁ w hw).t = -(W.a₃ + x₁ * W.a₁) / 2 := rfl

theorem legendreLambda_def (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.legendreLambda x₁ x₂ = (-W.b₂ / 4 - x₁ - x₂ - x₁) / (x₂ - x₁) := rfl

theorem thirdTwoTorsionX_legendreCurve (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).thirdTwoTorsionX 0 1 = t := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  simp only [thirdTwoTorsionX, legendreCurve, WeierstrassCurve.b₂]
  field_simp
  ring

/-- **Legendre parameter of the Legendre curve.** If $2 \ne 0$, the Legendre parameter of
$y^2 = x(x - 1)(x - t)$ at the roots $0$ and $1$ is $t$. -/
theorem legendreLambda_legendreCurve (h2 : (2 : F) ≠ 0) (t : F) :
    (legendreCurve t).legendreLambda 0 1 = t := by
  rw [legendreLambda, thirdTwoTorsionX_legendreCurve h2]; simp

theorem thirdTwoTorsionX_variableChange (h2 : (2 : F) ≠ 0) (C : VariableChange F)
    (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.thirdTwoTorsionX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
      = (C.u : F) ^ 2 * (C • W).thirdTwoTorsionX x₁ x₂ + C.r := by
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [thirdTwoTorsionX, variableChange_b₂, Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- **Invariance of the Legendre parameter.** If $2 \ne 0$, then for a variable change
$C = (u, r, s, t)$ the Legendre parameter of $W$ at $u^2x_1 + r$ and $u^2x_2 + r$ equals the
Legendre parameter of $C \cdot W$ at $x_1$ and $x_2$. -/
theorem legendreLambda_variableChange (h2 : (2 : F) ≠ 0) (C : VariableChange F)
    (W : WeierstrassCurve F) (x₁ x₂ : F) :
    W.legendreLambda ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).legendreLambda x₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  have hu2 : (C.u : F) ^ 2 ≠ 0 := pow_ne_zero 2 hu
  rw [legendreLambda, legendreLambda, thirdTwoTorsionX_variableChange h2]
  rw [show (C.u : F) ^ 2 * (C • W).thirdTwoTorsionX x₁ x₂ + C.r - ((C.u : F) ^ 2 * x₁ + C.r)
      = (C.u : F) ^ 2 * ((C • W).thirdTwoTorsionX x₁ x₂ - x₁) by ring,
    show (C.u : F) ^ 2 * x₂ + C.r - ((C.u : F) ^ 2 * x₁ + C.r) = (C.u : F) ^ 2 * (x₂ - x₁) by ring,
    mul_div_mul_left _ _ hu2]

theorem thirdTwoTorsionX_map {K : Type*} [Field K] (φ : F →+* K) (W : WeierstrassCurve F)
    (x₁ x₂ : F) :
    (W.map φ).thirdTwoTorsionX (φ x₁) (φ x₂) = φ (W.thirdTwoTorsionX x₁ x₂) := by
  simp [thirdTwoTorsionX, WeierstrassCurve.map_b₂, map_div₀, map_sub, map_neg, map_ofNat]

/-- **Base change of the Legendre parameter.** For a homomorphism of fields $\varphi : F \to K$,
the Legendre parameter of `W.map φ` at $\varphi(x_1)$ and $\varphi(x_2)$ is $\varphi$ of the
Legendre parameter of $W$ at $x_1$ and $x_2$. -/
theorem legendreLambda_map {K : Type*} [Field K] (φ : F →+* K) (W : WeierstrassCurve F)
    (x₁ x₂ : F) :
    (W.map φ).legendreLambda (φ x₁) (φ x₂) = φ (W.legendreLambda x₁ x₂) := by
  rw [legendreLambda, legendreLambda, thirdTwoTorsionX_map, map_div₀, map_sub, map_sub]

end WeierstrassCurve
