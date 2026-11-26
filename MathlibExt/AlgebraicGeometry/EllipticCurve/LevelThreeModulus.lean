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

`Definitions/Def_WeierstrassCurve_LevelThreeModulus.lean`
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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public section

/-!
# Level-three modulus and the Deuring form

A point of order three on an elliptic curve is a flex: its tangent line meets the curve there to
order three. Over a field, moving a flex `(x₁, y₁)` of `W` at which `2y₁ + a₁x₁ + a₃ ≠ 0`, so
that the tangent line is not vertical, to the origin, and its tangent line to `y = 0`, puts `W` in
the Deuring normal form `y² + αxy + βy = x³` (`WeierstrassCurve.deuringCurve`). This file
defines the quantities of that normalization (`deuringA₃`, `tangentSlopeNum`, `tangentSlope`,
`deuringA₁`, `flexForm`, `deuringVariableChange`) and the level-three coordinates
`levelThreeModulus`, `levelThreeAbscissa` and `levelThreeOrdinate` of the flex together with a
second point `(x₂, y₂)`. When `x₂ ≠ x₁`, they are the Deuring coefficient `α` and the coordinates
of the second point after the scaling `u = deuringA₃ x₁ y₁ / (x₂ - x₁)`, the one that sends its
abscissa to the Deuring coefficient `β`. When `x₂ = x₁` no scaling does that: the second abscissa
stays `0` while `β` is not `0`, as for the flex `(0, 0)` of `y² + y = x³` and the point
`(0, -1)`. The formulas still return values then (all three are `0`), but not coordinates of that
normalization.

## Main results

* `WeierstrassCurve.deuringVariableChange_smul`: a flex can be moved to Deuring form.
* `WeierstrassCurve.deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus`: the Deuring
  form in terms of the level-three coordinates, for `x₂ ≠ x₁`.
* `WeierstrassCurve.levelThreeModulus_variableChange` and its abscissa and ordinate versions:
  the level-three coordinates do not depend on the Weierstrass model.
* `WeierstrassCurve.levelThreeModulus_map` and `WeierstrassCurve.levelThreeModulus_map_of_isUnit`,
  with their abscissa and ordinate versions: compatibility with base change.
* `WeierstrassCurve.levelThreeModulus_deuringCurve` and its abscissa and ordinate versions: on a
  Deuring form with `β ≠ 0`, the level-three coordinates at the origin and the abscissa `β`
  recover its coefficients.

## Implementation notes

Quotients by `deuringA₃ x₁ y₁ = 2y₁ + a₁x₁ + a₃` use `Ring.inverse`. So when it is not a unit,
`tangentSlope`, `levelThreeModulus`, `levelThreeAbscissa` and `levelThreeOrdinate` are `0` and
`deuringA₁` is `a₁`. Over a field this happens exactly when `deuringA₃ x₁ y₁ = 0`, that is, when
`y₁ = negY x₁ y₁` (`deuringA₃_eq_sub_negY`); for a nonsingular point of the curve this means that
the point is its own negative.

The variable-change laws of `levelThreeModulus`, `levelThreeAbscissa` and `levelThreeOrdinate`
hold without hypotheses: the two denominators differ by a power of `u`, so when one is `0` both
sides are `0`. So do those of `deuringA₃`, `tangentSlopeNum` and `flexForm`, which are polynomial
identities. The laws of `tangentSlope` and `deuringA₁` (`tangentSlope_variableChange` and
`deuringA₁_variableChange`) need `deuringA₃` to be nonzero at the point: on `y² = x³ - x` at
`(0, 0)`, the variable change `(u, r, s, t) = (1, 0, 1, 0)` fixes the point and leaves both
denominators `0`, so both totalized slopes are `0`, and the two laws would read `0 = 0 + 1` and
`0 = 2`. The base-change laws along field homomorphisms hold without hypotheses; along a ring
homomorphism, those of the quotients need `deuringA₃ x₁ y₁` to be a unit.
-/

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-- **Deuring normal form.** For $\alpha, \beta$ in a commutative ring $R$, `deuringCurve α β` is
the Weierstrass curve $y^2 + \alpha xy + \beta y = x^3$, with discriminant
$\beta^3(\alpha^3 - 27\beta)$ (`deuringCurve_Δ`). Over a field with $\beta \ne 0$, the origin is
a nonsingular point of the curve, and its tangent line $y = 0$ meets the curve only there, to
order three, so the origin is a flex; when the curve is moreover elliptic, the origin is a point of
order three. Conversely, over a field `deuringVariableChange_smul` puts a Weierstrass curve in this
form, with a given point at the origin, when that point lies on the curve, satisfies
$2y + a_1x + a_3 \ne 0$ and has vanishing flex form, that is, when it is a flex whose tangent line
is not vertical. -/
def deuringCurve (α β : R) : WeierstrassCurve R := ⟨α, 0, β, 0, 0⟩

section deuringCurve

variable (α β : R)

@[simp] theorem deuringCurve_a₁ : (deuringCurve α β).a₁ = α := rfl
@[simp] theorem deuringCurve_a₂ : (deuringCurve α β).a₂ = 0 := rfl
@[simp] theorem deuringCurve_a₃ : (deuringCurve α β).a₃ = β := rfl
@[simp] theorem deuringCurve_a₄ : (deuringCurve α β).a₄ = 0 := rfl
@[simp] theorem deuringCurve_a₆ : (deuringCurve α β).a₆ = 0 := rfl

theorem deuringCurve_b₂ : (deuringCurve α β).b₂ = α ^ 2 := by
  simp [deuringCurve, WeierstrassCurve.b₂]

theorem deuringCurve_b₄ : (deuringCurve α β).b₄ = α * β := by
  simp [deuringCurve, WeierstrassCurve.b₄]

theorem deuringCurve_b₆ : (deuringCurve α β).b₆ = β ^ 2 := by
  simp [deuringCurve, WeierstrassCurve.b₆]

theorem deuringCurve_b₈ : (deuringCurve α β).b₈ = 0 := by
  simp [deuringCurve, WeierstrassCurve.b₈]

theorem deuringCurve_c₄ : (deuringCurve α β).c₄ = α * (α ^ 3 - 24 * β) := by
  simp only [WeierstrassCurve.c₄, deuringCurve_b₂, deuringCurve_b₄]; ring

/-- **Discriminant of the Deuring form.** The Weierstrass curve $y^2 + \alpha xy + \beta y = x^3$
has discriminant $\Delta = \beta^3(\alpha^3 - 27\beta)$. -/
theorem deuringCurve_Δ : (deuringCurve α β).Δ = β ^ 3 * (α ^ 3 - 27 * β) := by
  simp only [WeierstrassCurve.Δ, deuringCurve_b₂, deuringCurve_b₄, deuringCurve_b₆, deuringCurve_b₈]
  ring

/-- **Base change of the Deuring form.** For a ring homomorphism $f : R \to S$, the base change
of $y^2 + \alpha xy + \beta y = x^3$ along $f$ is $y^2 + f(\alpha)xy + f(\beta)y = x^3$. -/
theorem deuringCurve_map {S : Type*} [CommRing S] (f : R →+* S) :
    (deuringCurve α β).map f = deuringCurve (f α) (f β) := by
  simp [deuringCurve, WeierstrassCurve.map]

/-- **Discriminant under the level-three relation.** If $3\nu + \tau^2 + 3\tau + 3 = 0$, then the
Deuring form $y^2 + \tau xy + \nu y = x^3$ has discriminant $\nu^3(\tau + 3)^3$. -/
theorem deuringCurve_Δ_of_levelThree_rel {τ ν : R} (h : 3 * ν + τ ^ 2 + 3 * τ + 3 = 0) :
    (deuringCurve τ ν).Δ = ν ^ 3 * (τ + 3) ^ 3 := by
  rw [deuringCurve_Δ]
  have : τ ^ 3 - 27 * ν = (τ + 3) ^ 3 := by linear_combination (-9 : R) * h
  rw [this]

end deuringCurve

variable (W : WeierstrassCurve R)

/-- **The $y$-derivative $2y + a_1x + a_3$.** For a Weierstrass curve $W$ over a commutative ring
and $x, y$ in that ring, `W.deuringA₃ x y` is $2y + a_1x + a_3$. It is the partial derivative in
$y$ of the Weierstrass polynomial at $(x, y)$ (`deuringA₃_eq_evalEval_polynomialY`), and the
difference $y - y'$ for $y'$ = `W.toAffine.negY x y`, which is the ordinate of $-(x, y)$ when
$(x, y)$ is a nonsingular point of $W$ (`deuringA₃_eq_sub_negY`). At a point $(x, y)$ of $W$ over
a field where it is nonzero and the flex form vanishes, it is the coefficient $a_3$ of the Deuring
form before scaling (`deuringVariableChange_smul`). The quotients of this file divide by it. -/
def deuringA₃ (x y : R) : R := 2 * y + W.a₁ * x + W.a₃

/-- **Numerator of the tangent-slope quotient.** For a Weierstrass curve $W$ and $x, y$,
`W.tangentSlopeNum x y` is $3x^2 + 2a_2x + a_4 - a_1y$, the numerator of `tangentSlope`. It is
minus the partial derivative in $x$ of the Weierstrass polynomial at $(x, y)$
(`tangentSlopeNum_eq_neg_evalEval_polynomialX`). -/
def tangentSlopeNum (x y : R) : R := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y

/-- **Totalized tangent-slope quotient.** For a Weierstrass curve $W$ and any $x, y$,
`W.tangentSlope x y` is $(3x^2 + 2a_2x + a_4 - a_1y)/(2y + a_1x + a_3)$ with the division taken by
`Ring.inverse`, so the value is $0$ whenever $2y + a_1x + a_3$ is not a unit. Over a field with
$2y + a_1x + a_3 \ne 0$ it equals `W.toAffine.slope x x y y` (`tangentSlope_eq_slope`).

When $(x, y)$ is a point of $W$ and $2y + a_1x + a_3$ is a unit, the value is the slope of the
tangent line to $W$ at $(x, y)$. When $2y + a_1x + a_3 = 0$ the value $0$ is only the totalized
quotient. At a nonsingular point of $W$ over a field, $2y + a_1x + a_3$ is the partial derivative
in $y$ of the Weierstrass polynomial, so when it vanishes the partial derivative in $x$,
$a_1y - (3x^2 + 2a_2x + a_4)$, does not, and the tangent line is vertical: on $y^2 = x^3 - x$ at
$(0, 0)$ it is $x = 0$. At a singular point both partial derivatives vanish: on the cusp
$y^2 = x^3$ at $(0, 0)$ the tangent cone is the double line $y = 0$. -/
noncomputable def tangentSlope (x y : R) : R := W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x
  y)

/-- **The coefficient $a_1 + 2m$.** For a Weierstrass curve $W$ and $x, y$, `W.deuringA₁ x y` is
$a_1 + 2m$, where $m$ is `W.tangentSlope x y`. At a point $(x, y)$ of $W$ over a field where
$2y + a_1x + a_3 \ne 0$ and the flex form vanishes, it is the coefficient $a_1$ of the Deuring form
before scaling (`deuringVariableChange_smul`). Because `tangentSlope` is totalized, the value is
$a_1$ when $2y + a_1x + a_3$ is not a unit. -/
noncomputable def deuringA₁ (x y : R) : R := W.a₁ + 2 * W.tangentSlope x y

/-- **Flex form.** For a Weierstrass curve $W$ and $x, y$, write $n$ for `W.tangentSlopeNum x y`
and $d$ for `W.deuringA₃ x y`. Then `W.flexForm x y` is $n^2 + a_1nd - (a_2 + 3x)d^2$. When $d$ is
invertible this is $d^2(m^2 + a_1m - a_2 - 3x)$ for $m = n/d$. At a point $(x, y)$ of $W$ over a
field with $d \ne 0$, which is then nonsingular, $m$ is the slope of the tangent line, and the
factor $m^2 + a_1m - a_2 - 3x$ vanishes exactly when the tangent line meets $W$ to order three
there, that is, when $(x, y)$ is a flex. On the curve the flex form is $-\Psi_3(x)$
(`flexForm_eq_neg_eval_Ψ₃`). -/
def flexForm (x y : R) : R :=
  W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
    - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2

/-- **Variable change to Deuring form.** For a Weierstrass curve $W$, a point $(x_1, y_1)$ and a
unit $u$, `W.deuringVariableChange x₁ y₁ u` is the variable change
$(u, r, s, t) = (u, x_1, m, y_1)$, where $m$ is `W.tangentSlope x₁ y₁`; in coordinates,
$x = u^2x' + x_1$ and $y = u^3y' + u^2mx' + y_1$. It moves $(x_1, y_1)$ to the origin. When
$(x_1, y_1)$ is a point of $W$ at which $2y_1 + a_1x_1 + a_3$ is a unit, it also moves the tangent
line there to $y' = 0$; over a field, at such a point where the flex form vanishes, it gives the
Deuring form (`deuringVariableChange_smul`). -/
noncomputable def deuringVariableChange (x₁ y₁ : R) (u : Rˣ) : VariableChange R :=
  ⟨u, x₁, W.tangentSlope x₁ y₁, y₁⟩

/-- **Level-three modulus.** For a Weierstrass curve $W$, a point $(x_1, y_1)$ and an abscissa
$x_2$, `W.levelThreeModulus x₁ y₁ x₂` is $a(x_2 - x_1)/d$, where $a$ is `W.deuringA₁ x₁ y₁` and $d$
is `W.deuringA₃ x₁ y₁`, with the division taken by `Ring.inverse`: the value is $0$ when $d$ is not
a unit. When $(x_1, y_1)$ is a point of $W$ over a field at which $d \ne 0$ and the flex form
vanishes, and $x_2 \ne x_1$, it is the coefficient $\alpha$ of the Deuring form
$y^2 + \alpha xy + \beta y = x^3$ reached with the scaling $u = d/(x_2 - x_1)$
(`deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus`). -/
noncomputable def levelThreeModulus (x₁ y₁ x₂ : R) : R :=
  W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁)

/-- **Level-three abscissa.** For a Weierstrass curve $W$, a point $(x_1, y_1)$ and an abscissa
$x_2$, `W.levelThreeAbscissa x₁ y₁ x₂` is $(x_2 - x_1)^3/d^2$, where $d$ is `W.deuringA₃ x₁ y₁`,
with the division taken by `Ring.inverse`: the value is $0$ when $d$ is not a unit. Over a field
with $d \ne 0$ and $x_2 \ne x_1$ it is the abscissa that the scaling $u = d/(x_2 - x_1)$ of
`levelThreeModulus` gives to $x_2$. When moreover $(x_1, y_1)$ is a point of $W$ at which the flex
form vanishes, it is the coefficient $\beta$ of the Deuring form
(`deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus`). -/
noncomputable def levelThreeAbscissa (x₁ y₁ x₂ : R) : R :=
  (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2

/-- **Level-three ordinate.** For a Weierstrass curve $W$ and points $(x_1, y_1)$, $(x_2, y_2)$,
`W.levelThreeOrdinate x₁ y₁ x₂ y₂` is $(y_2 - y_1 - m(x_2 - x_1))(x_2 - x_1)^3/d^3$, where $m$ is
`W.tangentSlope x₁ y₁` and $d$ is `W.deuringA₃ x₁ y₁`, with the division taken by `Ring.inverse`:
the value is $0$ when $d$ is not a unit. Over a field with $d \ne 0$ and $x_2 \ne x_1$ it is the
ordinate that `W.deuringVariableChange x₁ y₁ u` with $u = d/(x_2 - x_1)$ gives to $(x_2, y_2)$. -/
noncomputable def levelThreeOrdinate (x₁ y₁ x₂ y₂ : R) : R :=
  (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^
    3

section ring

variable {W}

theorem deuringA₃_def (x y : R) : W.deuringA₃ x y = 2 * y + W.a₁ * x + W.a₃ := rfl

theorem tangentSlopeNum_def (x y : R) :
    W.tangentSlopeNum x y = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := rfl

theorem tangentSlope_def (x y : R) :
    W.tangentSlope x y = W.tangentSlopeNum x y * Ring.inverse (W.deuringA₃ x y) := rfl

theorem deuringA₁_def (x y : R) : W.deuringA₁ x y = W.a₁ + 2 * W.tangentSlope x y := rfl

theorem flexForm_def (x y : R) : W.flexForm x y =
    W.tangentSlopeNum x y ^ 2 + W.a₁ * W.tangentSlopeNum x y * W.deuringA₃ x y
      - (W.a₂ + 3 * x) * W.deuringA₃ x y ^ 2 := rfl

theorem levelThreeModulus_def (x₁ y₁ x₂ : R) : W.levelThreeModulus x₁ y₁ x₂ =
    W.deuringA₁ x₁ y₁ * (x₂ - x₁) * Ring.inverse (W.deuringA₃ x₁ y₁) := rfl

theorem levelThreeAbscissa_def (x₁ y₁ x₂ : R) : W.levelThreeAbscissa x₁ y₁ x₂ =
    (x₂ - x₁) ^ 3 * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 2 := rfl

theorem levelThreeOrdinate_def (x₁ y₁ x₂ y₂ : R) : W.levelThreeOrdinate x₁ y₁ x₂ y₂ =
    (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3
      * Ring.inverse (W.deuringA₃ x₁ y₁) ^ 3 := rfl

@[simp] theorem deuringVariableChange_u (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).u = u := rfl
@[simp] theorem deuringVariableChange_r (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).r = x₁ := rfl
@[simp] theorem deuringVariableChange_s (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).s = W.tangentSlope x₁ y₁ := rfl
@[simp] theorem deuringVariableChange_t (x₁ y₁ : R) (u : Rˣ) :
    (W.deuringVariableChange x₁ y₁ u).t = y₁ := rfl

theorem deuringA₃_eq_evalEval_polynomialY (x y : R) :
    W.deuringA₃ x y = W.toAffine.polynomialY.evalEval x y := by
  rw [Affine.evalEval_polynomialY]; rfl

theorem deuringA₃_eq_sub_negY (x y : R) : W.deuringA₃ x y = y - W.toAffine.negY x y := by
  rw [deuringA₃_def, Affine.negY]; change 2 * y + W.a₁ * x + W.a₃ = y - (-y - W.a₁ * x - W.a₃); ring

theorem tangentSlopeNum_eq_neg_evalEval_polynomialX (x y : R) :
    W.tangentSlopeNum x y = -W.toAffine.polynomialX.evalEval x y := by
  rw [Affine.evalEval_polynomialX, tangentSlopeNum_def]; change _ = -(W.a₁ * y - _); ring

theorem eval_Ψ₃ (x : R) :
    W.Ψ₃.eval x = 3 * x ^ 4 + W.b₂ * x ^ 3 + 3 * W.b₄ * x ^ 2 + 3 * W.b₆ * x + W.b₈ := by
  simp only [Ψ₃, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat]

theorem flexForm_add_eval_Ψ₃ (x y : R) :
    W.flexForm x y + W.Ψ₃.eval x = -(W.b₂ + 12 * x) * W.toAffine.polynomial.evalEval x y := by
  rw [eval_Ψ₃, Affine.evalEval_polynomial, flexForm_def, tangentSlopeNum_def, deuringA₃_def]
  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  change _ = -(W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) *
    (y ^ 2 + W.a₁ * x * y + W.a₃ * y - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆))
  ring

/-- **Flex form and the third division polynomial.** At a point $(x, y)$ of $W$, the flex form
equals $-\Psi_3(x)$, where $\Psi_3 = 3X^4 + b_2X^3 + 3b_4X^2 + 3b_6X + b_8$ is the third division
polynomial `W.Ψ₃`. -/
theorem flexForm_eq_neg_eval_Ψ₃ {x y : R} (h : W.toAffine.Equation x y) :
    W.flexForm x y = -W.Ψ₃.eval x := by
  have := flexForm_add_eval_Ψ₃ (W := W) x y
  rw [show W.toAffine.polynomial.evalEval x y = 0 from h, mul_zero] at this
  linear_combination this

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

theorem deuringA₃_map (x y : R) : (W.map f).deuringA₃ (f x) (f y) = f (W.deuringA₃ x y) := by
  simp [deuringA₃_def, map_ofNat]

theorem tangentSlopeNum_map (x y : R) :
    (W.map f).tangentSlopeNum (f x) (f y) = f (W.tangentSlopeNum x y) := by
  simp [tangentSlopeNum_def, map_ofNat]

theorem flexForm_map (x y : R) : (W.map f).flexForm (f x) (f y) = f (W.flexForm x y) := by
  simp [flexForm_def, tangentSlopeNum_map, deuringA₃_map, map_ofNat]

theorem tangentSlope_map_of_isUnit {x y : R} (h : IsUnit (W.deuringA₃ x y)) :
    (W.map f).tangentSlope (f x) (f y) = f (W.tangentSlope x y) := by
  rw [tangentSlope_def, tangentSlope_def, tangentSlopeNum_map, deuringA₃_map, map_mul,
    h.map_ringInverse f]

theorem deuringA₁_map_of_isUnit {x y : R} (h : IsUnit (W.deuringA₃ x y)) :
    (W.map f).deuringA₁ (f x) (f y) = f (W.deuringA₁ x y) := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_map_of_isUnit f h]; simp [map_ofNat]

/-- **Base change of the level-three modulus over rings.** Let $f : R \to S$ be a ring
homomorphism and $(x_1, y_1)$ a point at which `W.deuringA₃ x₁ y₁` is a unit. Then the level-three
modulus of `W.map f` at $(f(x_1), f(y_1))$ and $f(x_2)$ is the image under $f$ of the level-three
modulus of $W$ at $(x_1, y_1)$ and $x_2$. The unit hypothesis cannot be dropped: $f$ can send a
nonunit denominator, where the totalized value is $0$, to a unit. -/
theorem levelThreeModulus_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ : R) :
    (W.map f).levelThreeModulus (f x₁) (f y₁) (f x₂) = f (W.levelThreeModulus x₁ y₁ x₂) := by
  rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₁_map_of_isUnit f h, deuringA₃_map,
    ← h.map_ringInverse f]
  simp

/-- **Base change of the level-three abscissa over rings.** Let $f : R \to S$ be a ring
homomorphism and $(x_1, y_1)$ a point at which `W.deuringA₃ x₁ y₁` is a unit. Then the level-three
abscissa of `W.map f` at $(f(x_1), f(y_1))$ and $f(x_2)$ is the image under $f$ of the level-three
abscissa of $W$ at $(x_1, y_1)$ and $x_2$. As for `levelThreeModulus_map_of_isUnit`, the unit
hypothesis cannot be dropped. -/
theorem levelThreeAbscissa_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ : R) :
    (W.map f).levelThreeAbscissa (f x₁) (f y₁) (f x₂) = f (W.levelThreeAbscissa x₁ y₁ x₂) := by
  rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_map, ← h.map_ringInverse f]
  simp

/-- **Base change of the level-three ordinate over rings.** Let $f : R \to S$ be a ring
homomorphism and $(x_1, y_1)$ a point at which `W.deuringA₃ x₁ y₁` is a unit. Then the level-three
ordinate of `W.map f` at $(f(x_1), f(y_1))$ and $(f(x_2), f(y_2))$ is the image under $f$ of the
level-three ordinate of $W$ at $(x_1, y_1)$ and $(x_2, y_2)$. As for
`levelThreeModulus_map_of_isUnit`, the unit hypothesis cannot be dropped. -/
theorem levelThreeOrdinate_map_of_isUnit {x₁ y₁ : R} (h : IsUnit (W.deuringA₃ x₁ y₁)) (x₂ y₂ : R) :
    (W.map f).levelThreeOrdinate (f x₁) (f y₁) (f x₂) (f y₂) = f (W.levelThreeOrdinate x₁ y₁ x₂ y₂)
      := by
  rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_map, tangentSlope_map_of_isUnit f h,
    ← h.map_ringInverse f]
  simp

end map

theorem deuringA₃_variableChange (C : VariableChange R) (x y : R) :
    W.deuringA₃ ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 3 * (C • W).deuringA₃ x y := by
  simp only [deuringA₃_def, variableChange_a₁, variableChange_a₃]
  linear_combination -((W.a₁ + 2 * C.s) * x * (C.u : R) ^ 2) * C.u.inv_mul
    - (W.a₃ + C.r * W.a₁ + 2 * C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul

theorem tangentSlopeNum_variableChange (C : VariableChange R) (x y : R) :
    W.tangentSlopeNum ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 4 * (C • W).tangentSlopeNum x y + C.s * (C.u : R) ^ 3 * (C • W).deuringA₃ x y
        := by
  simp only [tangentSlopeNum_def, deuringA₃_def, variableChange_a₁, variableChange_a₂,
    variableChange_a₃, variableChange_a₄]
  linear_combination -(2 * (C.u : R) ^ 2 * (W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * x)
      * pow_mul_pow_eq_one 2 C.u.inv_mul
    - (W.a₄ - C.s * W.a₃ + 2 * C.r * W.a₂ - (C.t + C.r * C.s) * W.a₁ + 3 * C.r ^ 2 - 2 * C.s * C.t)
      * pow_mul_pow_eq_one 4 C.u.inv_mul
    + ((C.u : R) ^ 3 * (W.a₁ + 2 * C.s) * y - C.s * (C.u : R) ^ 2 * (W.a₁ + 2 * C.s) * x)
      * C.u.inv_mul
    - C.s * (W.a₃ + C.r * W.a₁ + 2 * C.t) * pow_mul_pow_eq_one 3 C.u.inv_mul

theorem flexForm_variableChange (C : VariableChange R) (x y : R) :
    W.flexForm ((C.u : R) ^ 2 * x + C.r) ((C.u : R) ^ 3 * y + (C.u : R) ^ 2 * C.s * x + C.t)
      = (C.u : R) ^ 8 * (C • W).flexForm x y := by
  rw [flexForm_def, flexForm_def, tangentSlopeNum_variableChange, deuringA₃_variableChange]
  have ha₁ : W.a₁ = (C.u : R) * (C • W).a₁ - 2 * C.s := by
    rw [variableChange_a₁]; linear_combination -(W.a₁ + 2 * C.s) * C.u.inv_mul
  have ha₂ : W.a₂ + 3 * ((C.u : R) ^ 2 * x + C.r)
      = (C.u : R) ^ 2 * ((C • W).a₂ + 3 * x) + C.s * W.a₁ + C.s ^ 2 := by
    rw [variableChange_a₂]
    linear_combination -(W.a₂ - C.s * W.a₁ + 3 * C.r - C.s ^ 2) * pow_mul_pow_eq_one 2 C.u.inv_mul
  rw [ha₂, ha₁]
  ring

end ring

section field

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

theorem tangentSlope_eq_div (x y : F) :
    W.tangentSlope x y = W.tangentSlopeNum x y / W.deuringA₃ x y := by
  rw [tangentSlope_def, Ring.inverse_eq_inv, div_eq_mul_inv]

/-- **Agreement with Mathlib's tangent slope.** Over a field, if $2y + a_1x + a_3 \ne 0$, then
`W.tangentSlope x y` equals `W.toAffine.slope x x y y`. -/
theorem tangentSlope_eq_slope [DecidableEq F] {x y : F} (h : W.deuringA₃ x y ≠ 0) :
    W.tangentSlope x y = W.toAffine.slope x x y y := by
  have hy : y ≠ W.toAffine.negY x y := by
    intro hy; apply h; rw [deuringA₃_eq_sub_negY, ← hy, sub_self]
  rw [Affine.slope_of_Y_ne rfl hy, ← deuringA₃_eq_sub_negY, tangentSlope_eq_div]; rfl

theorem deuringA₁_eq_div (x y : F) :
    W.deuringA₁ x y = (W.a₁ * W.deuringA₃ x y + 2 * W.tangentSlopeNum x y) / W.deuringA₃ x y ∨
      W.deuringA₃ x y = 0 := by
  by_cases h : W.deuringA₃ x y = 0
  · exact Or.inr h
  · left; rw [deuringA₁_def, tangentSlope_eq_div]; field_simp

theorem levelThreeModulus_eq_div (x₁ y₁ x₂ : F) : W.levelThreeModulus x₁ y₁ x₂ =
    (W.a₁ * W.deuringA₃ x₁ y₁ + 2 * W.tangentSlopeNum x₁ y₁) * (x₂ - x₁) / W.deuringA₃ x₁ y₁ ^ 2 :=
      by
  rw [levelThreeModulus_def, deuringA₁_def, tangentSlope_eq_div, Ring.inverse_eq_inv]
  by_cases h : W.deuringA₃ x₁ y₁ = 0
  · rw [h]; simp
  · field_simp

theorem levelThreeAbscissa_eq_div (x₁ y₁ x₂ : F) :
    W.levelThreeAbscissa x₁ y₁ x₂ = (x₂ - x₁) ^ 3 / W.deuringA₃ x₁ y₁ ^ 2 := by
  rw [levelThreeAbscissa_def, Ring.inverse_eq_inv, div_eq_mul_inv, inv_pow]

theorem levelThreeOrdinate_eq_div (x₁ y₁ x₂ y₂ : F) : W.levelThreeOrdinate x₁ y₁ x₂ y₂ =
    (y₂ - y₁ - W.tangentSlope x₁ y₁ * (x₂ - x₁)) * (x₂ - x₁) ^ 3 / W.deuringA₃ x₁ y₁ ^ 3 := by
  rw [levelThreeOrdinate_def, Ring.inverse_eq_inv, div_eq_mul_inv, inv_pow]

section map

variable {K : Type*} [Field K] (φ : F →+* K)

theorem tangentSlope_map (x y : F) : (W.map φ).tangentSlope (φ x) (φ y) = φ (W.tangentSlope x y) :=
  by
  rw [tangentSlope_eq_div, tangentSlope_eq_div, tangentSlopeNum_map, deuringA₃_map, map_div₀]

theorem deuringA₁_map (x y : F) : (W.map φ).deuringA₁ (φ x) (φ y) = φ (W.deuringA₁ x y) := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_map]; simp [map_ofNat]

/-- **Base change of the level-three modulus over fields.** For a homomorphism of fields
$\varphi : F \to K$, the level-three modulus of `W.map φ` at $(\varphi(x_1), \varphi(y_1))$ and
$\varphi(x_2)$ is $\varphi$ of the level-three modulus of $W$ at $(x_1, y_1)$ and $x_2$. No
hypothesis is needed: $\varphi$ is injective, so a denominator is zero exactly when its image
is. -/
theorem levelThreeModulus_map (x₁ y₁ x₂ : F) :
    (W.map φ).levelThreeModulus (φ x₁) (φ y₁) (φ x₂) = φ (W.levelThreeModulus x₁ y₁ x₂) := by
  rw [levelThreeModulus_eq_div, levelThreeModulus_eq_div, tangentSlopeNum_map, deuringA₃_map]
  simp [map_ofNat, map_div₀]

/-- **Base change of the level-three abscissa over fields.** For a homomorphism of fields
$\varphi : F \to K$, the level-three abscissa of `W.map φ` at $(\varphi(x_1), \varphi(y_1))$ and
$\varphi(x_2)$ is $\varphi$ of the level-three abscissa of $W$ at $(x_1, y_1)$ and $x_2$, with no
hypothesis on the denominator. -/
theorem levelThreeAbscissa_map (x₁ y₁ x₂ : F) :
    (W.map φ).levelThreeAbscissa (φ x₁) (φ y₁) (φ x₂) = φ (W.levelThreeAbscissa x₁ y₁ x₂) := by
  rw [levelThreeAbscissa_eq_div, levelThreeAbscissa_eq_div, deuringA₃_map]
  simp [map_div₀]

/-- **Base change of the level-three ordinate over fields.** For a homomorphism of fields
$\varphi : F \to K$, the level-three ordinate of `W.map φ` at $(\varphi(x_1), \varphi(y_1))$ and
$(\varphi(x_2), \varphi(y_2))$ is $\varphi$ of the level-three ordinate of $W$ at $(x_1, y_1)$ and
$(x_2, y_2)$, with no hypothesis on the denominator. -/
theorem levelThreeOrdinate_map (x₁ y₁ x₂ y₂ : F) :
    (W.map φ).levelThreeOrdinate (φ x₁) (φ y₁) (φ x₂) (φ y₂) = φ (W.levelThreeOrdinate x₁ y₁ x₂ y₂)
      := by
  rw [levelThreeOrdinate_eq_div, levelThreeOrdinate_eq_div, deuringA₃_map, tangentSlope_map]
  simp [map_div₀]

end map

/-- **Normalization of a flex to Deuring form.** Let $W$ be a Weierstrass curve over a field and
$(x_1, y_1)$ a point of $W$ at which $d$ = `W.deuringA₃ x₁ y₁` is nonzero and the flex form
vanishes. Then for every unit $u$ the variable change `W.deuringVariableChange x₁ y₁ u` carries $W$
to the Deuring form $y^2 + (a/u)xy + (d/u^3)y = x^3$, where $a$ is `W.deuringA₁ x₁ y₁`. -/
theorem deuringVariableChange_smul {x₁ y₁ : F} (heq : W.toAffine.Equation x₁ y₁)
    (hΨ : W.deuringA₃ x₁ y₁ ≠ 0) (hflex : W.flexForm x₁ y₁ = 0) (u : Fˣ) :
    W.deuringVariableChange x₁ y₁ u • W =
      deuringCurve (W.deuringA₁ x₁ y₁ / u) (W.deuringA₃ x₁ y₁ / (u : F) ^ 3) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  rw [Affine.equation_iff] at heq
  set m := W.tangentSlope x₁ y₁ with hm
  have hmd : m * W.deuringA₃ x₁ y₁ = W.tangentSlopeNum x₁ y₁ := by
    rw [hm, tangentSlope_eq_div, div_mul_cancel₀ _ hΨ]
  have hfl : m ^ 2 + W.a₁ * m - W.a₂ - 3 * x₁ = 0 := by
    have h : (m ^ 2 + W.a₁ * m - W.a₂ - 3 * x₁) * W.deuringA₃ x₁ y₁ ^ 2 = W.flexForm x₁ y₁ := by
      rw [flexForm_def, ← hmd]; ring
    rw [hflex] at h
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hΨ)
  rw [deuringA₃_def] at hmd hΨ
  rw [tangentSlopeNum_def] at hmd
  ext
  · simp only [variableChange_a₁, deuringVariableChange, deuringCurve_a₁, deuringA₁_def,
      Units.val_inv_eq_inv_val, ← hm]
    field_simp
  · simp only [variableChange_a₂, deuringVariableChange, deuringCurve_a₂, Units.val_inv_eq_inv_val,
      ← hm]
    rw [show W.a₂ - m * W.a₁ + 3 * x₁ - m ^ 2 = 0 by linear_combination -hfl, mul_zero]
  · simp only [variableChange_a₃, deuringVariableChange, deuringCurve_a₃, deuringA₃_def,
      Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [variableChange_a₄, deuringVariableChange, deuringCurve_a₄, Units.val_inv_eq_inv_val,
      ← hm]
    rw [show W.a₄ - m * W.a₃ + 2 * x₁ * W.a₂ - (y₁ + x₁ * m) * W.a₁ + 3 * x₁ ^ 2 - 2 * m * y₁ = 0 by
      linear_combination -hmd, mul_zero]
  · simp only [variableChange_a₆, deuringVariableChange, deuringCurve_a₆, Units.val_inv_eq_inv_val]
    rw [show W.a₆ + x₁ * W.a₄ + x₁ ^ 2 * W.a₂ + x₁ ^ 3 - y₁ * W.a₃ - y₁ ^ 2 - x₁ * y₁ * W.a₁ = 0 by
      linear_combination -heq, mul_zero]

/-- **Deuring form in level-three coordinates.** Under the hypotheses of
`deuringVariableChange_smul`, let $x_2 \ne x_1$ and let $u$ be the unit $d/(x_2 - x_1)$. Then
`W.deuringVariableChange x₁ y₁ u` carries $W$ to $y^2 + \alpha xy + \beta y = x^3$, where $\alpha$
is `W.levelThreeModulus x₁ y₁ x₂` and $\beta$ is `W.levelThreeAbscissa x₁ y₁ x₂`. -/
theorem deuringVariableChange_smul_eq_deuringCurve_levelThreeModulus {x₁ y₁ x₂ : F}
    (heq : W.toAffine.Equation x₁ y₁) (hΨ : W.deuringA₃ x₁ y₁ ≠ 0) (hflex : W.flexForm x₁ y₁ = 0)
    (hx : x₁ ≠ x₂) (u : Fˣ) (hu : (u : F) = W.deuringA₃ x₁ y₁ / (x₂ - x₁)) :
    W.deuringVariableChange x₁ y₁ u • W =
      deuringCurve (W.levelThreeModulus x₁ y₁ x₂) (W.levelThreeAbscissa x₁ y₁ x₂) := by
  have hd : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  rw [deuringVariableChange_smul heq hΨ hflex u, hu, levelThreeModulus_def, levelThreeAbscissa_def,
    Ring.inverse_eq_inv]
  congr 1
  · field_simp
  · field_simp

theorem tangentSlope_variableChange (C : VariableChange F) {x y : F} (h : (C • W).deuringA₃ x y ≠
  0) :
    W.tangentSlope ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).tangentSlope x y + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [tangentSlope_eq_div, tangentSlope_eq_div, tangentSlopeNum_variableChange,
    deuringA₃_variableChange]
  field_simp

theorem deuringA₁_variableChange (C : VariableChange F) {x y : F} (h : (C • W).deuringA₃ x y ≠ 0) :
    W.deuringA₁ ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) * (C • W).deuringA₁ x y := by
  rw [deuringA₁_def, deuringA₁_def, tangentSlope_variableChange C h, variableChange_a₁,
    Units.val_inv_eq_inv_val]
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  field_simp
  ring

/-- **Invariance of the level-three modulus.** Let $C = (u, r, s, t)$ be a variable change over a
field. The level-three modulus of $W$ at the images $(u^2x_1 + r, u^3y_1 + u^2sx_1 + t)$ of
$(x_1, y_1)$ and $u^2x_2 + r$ of $x_2$ equals the level-three modulus of $C \cdot W$ at
$(x_1, y_1)$ and $x_2$. No hypothesis is needed: the two denominators differ by the factor $u^3$,
so when one vanishes both values are $0$. -/
theorem levelThreeModulus_variableChange (C : VariableChange F) (x₁ y₁ x₂ : F) :
    W.levelThreeModulus ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ +
      C.t)
        ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).levelThreeModulus x₁ y₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeModulus_def, levelThreeModulus_def, deuringA₃_variableChange,
      deuringA₁_variableChange C h, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    field_simp
    ring

/-- **Invariance of the level-three abscissa.** Let $C = (u, r, s, t)$ be a variable change over
a field. The level-three abscissa of $W$ at the images $(u^2x_1 + r, u^3y_1 + u^2sx_1 + t)$ of
$(x_1, y_1)$ and $u^2x_2 + r$ of $x_2$ equals the level-three abscissa of $C \cdot W$ at
$(x_1, y_1)$ and $x_2$, with no hypothesis on the denominator. -/
theorem levelThreeAbscissa_variableChange (C : VariableChange F) (x₁ y₁ x₂ : F) :
    W.levelThreeAbscissa ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁
      + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r)
      = (C • W).levelThreeAbscissa x₁ y₁ x₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeAbscissa_def, levelThreeAbscissa_def, deuringA₃_variableChange,
    Ring.inverse_eq_inv,
      Ring.inverse_eq_inv]
    field_simp
    ring

/-- **Invariance of the level-three ordinate.** Let $C = (u, r, s, t)$ be a variable change over
a field. The level-three ordinate of $W$ at the images under $(x, y) \mapsto
(u^2x + r, u^3y + u^2sx + t)$ of $(x_1, y_1)$ and $(x_2, y_2)$ equals the level-three ordinate of
$C \cdot W$ at $(x_1, y_1)$ and $(x_2, y_2)$, with no hypothesis on the denominator. -/
theorem levelThreeOrdinate_variableChange (C : VariableChange F) (x₁ y₁ x₂ y₂ : F) :
    W.levelThreeOrdinate ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁
      + C.t)
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C • W).levelThreeOrdinate x₁ y₁ x₂ y₂ := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases h : (C • W).deuringA₃ x₁ y₁ = 0
  · rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_variableChange, h]; simp
  · rw [levelThreeOrdinate_def, levelThreeOrdinate_def, deuringA₃_variableChange,
      tangentSlope_variableChange C h, Ring.inverse_eq_inv, Ring.inverse_eq_inv]
    field_simp
    ring

theorem deuringA₃_deuringCurve_zero (τ ν : F) : (deuringCurve τ ν).deuringA₃ 0 0 = ν := by
  simp [deuringA₃_def]

theorem tangentSlope_deuringCurve_zero (τ ν : F) : (deuringCurve τ ν).tangentSlope 0 0 = 0 := by
  simp [tangentSlope_eq_div, tangentSlopeNum_def]

/-- **Modulus of a Deuring form.** If $\nu \ne 0$, the level-three modulus of
$y^2 + \tau xy + \nu y = x^3$ at the origin and the abscissa $\nu$ is $\tau$. -/
theorem levelThreeModulus_deuringCurve {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeModulus 0 0 ν = τ := by
  rw [levelThreeModulus_def, deuringA₁_def, tangentSlope_deuringCurve_zero,
    deuringA₃_deuringCurve_zero,
    Ring.inverse_eq_inv]
  simp only [deuringCurve_a₁, mul_zero, add_zero, sub_zero]
  field_simp

/-- **Abscissa of a Deuring form.** If $\nu \ne 0$, the level-three abscissa of
$y^2 + \tau xy + \nu y = x^3$ at the origin and the abscissa $\nu$ is $\nu$. -/
theorem levelThreeAbscissa_deuringCurve {τ ν : F} (hν : ν ≠ 0) :
    (deuringCurve τ ν).levelThreeAbscissa 0 0 ν = ν := by
  rw [levelThreeAbscissa_eq_div, deuringA₃_deuringCurve_zero, sub_zero]
  field_simp

/-- **Ordinate of a Deuring form.** If $\nu \ne 0$, then for every $\eta$ the level-three ordinate
of $y^2 + \tau xy + \nu y = x^3$ at the origin and the point $(\nu, \eta)$ is $\eta$. -/
theorem levelThreeOrdinate_deuringCurve {τ ν : F} (hν : ν ≠ 0) (η : F) :
    (deuringCurve τ ν).levelThreeOrdinate 0 0 ν η = η := by
  rw [levelThreeOrdinate_eq_div, deuringA₃_deuringCurve_zero, tangentSlope_deuringCurve_zero]
  field_simp
  ring

/-- **Flex form of a Deuring form at the abscissa $\nu$.** For $y^2 + \tau xy + \nu y = x^3$ and
every $\eta$, the flex form at $(\nu, \eta)$ equals
$-(\tau^2 + 12\nu)P(\nu, \eta) - \nu^3(3\nu + \tau^2 + 3\tau + 3)$, where $P$ is the Weierstrass
polynomial. So at a point $(\nu, \eta)$ of the curve with $\nu \ne 0$ the flex form vanishes
exactly when $3\nu + \tau^2 + 3\tau + 3 = 0$. -/
theorem flexForm_deuringCurve (τ ν η : F) :
    (deuringCurve τ ν).flexForm ν η =
      -(τ ^ 2 + 12 * ν) * (deuringCurve τ ν).toAffine.polynomial.evalEval ν η
        - ν ^ 3 * (3 * ν + τ ^ 2 + 3 * τ + 3) := by
  rw [Affine.evalEval_polynomial, flexForm_def, tangentSlopeNum_def, deuringA₃_def]
  simp only [deuringCurve_a₁, deuringCurve_a₂, deuringCurve_a₃, deuringCurve_a₄, deuringCurve_a₆]
  change _ = -(τ ^ 2 + 12 * ν) * (η ^ 2 + τ * ν * η + ν * η - (ν ^ 3 + 0 * ν ^ 2 + 0 * ν + 0)) - _
  ring

end field

end WeierstrassCurve
