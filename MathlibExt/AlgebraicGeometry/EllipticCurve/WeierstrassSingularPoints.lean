/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Tactic.LinearCombination

/-!
# Singular points of Weierstrass cubics

Let `W` be a Weierstrass curve over a field, with projective cubic
`C : Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`. Over an algebraically closed field:

1. `C` is nonsingular if and only if `Δ ≠ 0`;
2. if `Δ = 0`, then `C` has exactly one singular point `S`, `S ≠ (0 : 1 : 0)`, and `S` is a node
   if `c₄ ≠ 0` and a cusp if `c₄ = 0`.

The results hold in every characteristic, including `2` and `3`.

## Main definitions

For a Weierstrass curve `W` over a field and an affine point `(x₀, y₀)`, following Milne,
*Elliptic Curves*, Chapter I, §1:

* `WeierstrassCurve.polynomialAt`: the polynomial `f(X + x₀, Y + y₀)`, whose homogeneous
  components are the `fᵢ` of Milne's eq. (1), p. 8.
* `WeierstrassCurve.IsDoublePoint`: a point of multiplicity `2`.
* `WeierstrassCurve.IsTangentLine`: a tangent line at a double point, given by a linear factor
  of the degree-two part.
* `WeierstrassCurve.lineIntersectionNumber`: the intersection number of a line through the
  point with the curve, as the order of vanishing of the restriction of `f` to the line.
* `WeierstrassCurve.IsNode`, `WeierstrassCurve.IsCusp`: nodes and cusps, for curves over an
  algebraically closed field, where every tangent line is defined over the field.
* `WeierstrassCurve.IsSingularPoint`, `WeierstrassCurve.IsProjectiveNode`,
  `WeierstrassCurve.IsProjectiveCusp`: the projective versions.

## Main statements

* `WeierstrassCurve.singular_points_of_weierstrass_cubic`: both parts over an algebraically
  closed field `K` containing the base field `F`.
* `WeierstrassCurve.map_nonsingular_iff_Δ_ne_zero`: part 1 over an algebraically closed field
  `K` containing the base field `F`.
* `WeierstrassCurve.existsUnique_isSingularPoint_map`: part 2 over such a `K`.
* `WeierstrassCurve.nonsingular_iff_Δ_ne_zero`, `WeierstrassCurve.existsUnique_isSingularPoint`
  and `WeierstrassCurve.isProjectiveNode_and_isProjectiveCusp`: the same statements for a curve
  over an algebraically closed field.
* `WeierstrassCurve.isDoublePoint_iff`: the singular points of the affine curve are exactly its
  double points.

## References

* J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, author's version
  <https://www.jmilne.org/math/Books/EC2.pdf>: Chapter I, §1, p. 8 (multiplicity, tangent lines,
  nodes), pp. 9–10 (intersection numbers, Proposition 1.8, Lemma 1.11), Remark 1.12, p. 11
  (cusps); Chapter II, Theorem 2.4(a), p. 52, and §3, pp. 57–59.
* J. Tate, *The arithmetic of elliptic curves*, Invent. Math. 23 (1974), p. 182.
-/

@[expose] public section

open MvPolynomial

namespace WeierstrassCurve

section Local

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The affine Weierstrass polynomial
`f(X, Y) = Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)`, as a polynomial in the two variables
`X = X 0` and `Y = X 1`. -/
noncomputable def affineMvPolynomial : MvPolynomial (Fin 2) F :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 + C W.a₃ * X 1 -
    (X 0 ^ 3 + C W.a₂ * X 0 ^ 2 + C W.a₄ * X 0 + C W.a₆)

lemma eval_affineMvPolynomial (x y : F) :
    eval ![x, y] W.affineMvPolynomial = W.toAffine.polynomial.evalEval x y := by
  simp [affineMvPolynomial, Affine.evalEval_polynomial]

/-- The polynomial `f(X + x₀, Y + y₀)`, i.e. the affine Weierstrass polynomial written as a
polynomial in `X - x₀` and `Y - y₀`, as in Milne, *Elliptic Curves*, Chapter I, §1, eq. (1),
p. 8. -/
noncomputable def polynomialAt (x₀ y₀ : F) : MvPolynomial (Fin 2) F :=
  aeval (fun i => X i + C (![x₀, y₀] i)) W.affineMvPolynomial

/-- The quadratic form `Y² + a₁XY - (3x₀ + a₂)X²`: the degree-two part of `f(X + x₀, Y + y₀)`. -/
noncomputable def quadraticPart (x₀ : F) : MvPolynomial (Fin 2) F :=
  X 1 ^ 2 + C W.a₁ * X 0 * X 1 - C (3 * x₀ + W.a₂) * X 0 ^ 2

lemma polynomialAt_eq (x₀ y₀ : F) :
    W.polynomialAt x₀ y₀ =
      C (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) +
        (C (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) * X 0 +
          C (2 * y₀ + W.a₁ * x₀ + W.a₃) * X 1) +
        W.quadraticPart x₀ - X 0 ^ 3 := by
  simp only [polynomialAt, affineMvPolynomial, quadraticPart, map_add, map_sub, map_mul,
    map_pow, aeval_X, aeval_C, algebraMap_eq, map_ofNat, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

private lemma isHomogeneous_linear (p q : F) :
    (C p * X 0 + C q * X 1 : MvPolynomial (Fin 2) F).IsHomogeneous 1 :=
  ((isHomogeneous_X F 0).C_mul p).add ((isHomogeneous_X F 1).C_mul q)

private lemma isHomogeneous_quadraticPart (x₀ : F) : (W.quadraticPart x₀).IsHomogeneous 2 := by
  refine IsHomogeneous.sub (IsHomogeneous.add (isHomogeneous_X_pow _ _) ?_)
    ((isHomogeneous_X_pow _ _).C_mul _)
  exact ((isHomogeneous_X F 0).C_mul _).mul (isHomogeneous_X F 1)

private lemma homogeneousComponent_cubic {p₀ p₁ p₂ p₃ : MvPolynomial (Fin 2) F}
    (h₀ : p₀.IsHomogeneous 0) (h₁ : p₁.IsHomogeneous 1) (h₂ : p₂.IsHomogeneous 2)
    (h₃ : p₃.IsHomogeneous 3) (n : ℕ) :
    homogeneousComponent n (p₀ + p₁ + p₂ - p₃) =
      (if n = 0 then p₀ else 0) + (if n = 1 then p₁ else 0) + (if n = 2 then p₂ else 0) -
        (if n = 3 then p₃ else 0) := by
  simp only [map_add, map_sub]
  rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h₀),
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h₁),
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h₂),
    homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 h₃)]

private lemma homogeneousComponent_polynomialAt (x₀ y₀ : F) (n : ℕ) :
    homogeneousComponent n (W.polynomialAt x₀ y₀) =
      (if n = 0 then
        C (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆))
        else 0) +
      (if n = 1 then C (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) * X 0 +
          C (2 * y₀ + W.a₁ * x₀ + W.a₃) * X 1 else 0) +
      (if n = 2 then W.quadraticPart x₀ else 0) - (if n = 3 then X 0 ^ 3 else 0) := by
  rw [polynomialAt_eq]
  exact homogeneousComponent_cubic (isHomogeneous_C _ _) (isHomogeneous_linear _ _)
    (W.isHomogeneous_quadraticPart x₀) (isHomogeneous_X_pow 0 3) n

lemma homogeneousComponent_zero_polynomialAt (x₀ y₀ : F) :
    homogeneousComponent 0 (W.polynomialAt x₀ y₀) =
      C (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
  rw [homogeneousComponent_polynomialAt]; simp

lemma homogeneousComponent_one_polynomialAt (x₀ y₀ : F) :
    homogeneousComponent 1 (W.polynomialAt x₀ y₀) =
      C (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) * X 0 +
        C (2 * y₀ + W.a₁ * x₀ + W.a₃) * X 1 := by
  rw [homogeneousComponent_polynomialAt]; simp

lemma homogeneousComponent_two_polynomialAt (x₀ y₀ : F) :
    homogeneousComponent 2 (W.polynomialAt x₀ y₀) = W.quadraticPart x₀ := by
  rw [homogeneousComponent_polynomialAt]; simp

/-- `(x₀, y₀)` is a *double point* of the affine curve `f = 0`: writing `f = f₀ + f₁ + f₂ + ⋯`
with `fᵢ` homogeneous of degree `i` in `X - x₀`, `Y - y₀`, the point lies on the curve
(`f₀ = 0`), is singular (`f₁ = 0`), and `f₂ ≠ 0`, so that its multiplicity is `2`
(Milne, *Elliptic Curves*, Chapter I, §1, p. 8). -/
def IsDoublePoint (x₀ y₀ : F) : Prop :=
  homogeneousComponent 0 (W.polynomialAt x₀ y₀) = 0 ∧
    homogeneousComponent 1 (W.polynomialAt x₀ y₀) = 0 ∧
    homogeneousComponent 2 (W.polynomialAt x₀ y₀) ≠ 0

/-- The line `c(X - x₀) + d(Y - y₀) = 0`, with `(c, d) ≠ 0` and coefficients in `F`, is a
*tangent line* at the double point `(x₀, y₀)`: `(x₀, y₀)` is a double point
(`WeierstrassCurve.IsDoublePoint`), and the linear form `c(X - x₀) + d(Y - y₀)` divides the
degree-two part `f₂` (Milne, *Elliptic Curves*, Chapter I, §1, p. 8: at a singular point of
multiplicity `m`, the tangent lines are the lines `Lᵢ = 0` for the linear factors `Lᵢ` of `f_m`
over an algebraic closure, here `m = 2`). Over a field that is not algebraically closed, this
captures only the tangent lines defined over `F`. A line is recorded by its coefficient vector
`(c, d)`, which is determined by the line up to a nonzero scalar; accordingly, in `IsNode` and
`IsCusp` two tangent lines `(c, d)` and `(c', d')` are distinct when `c * d' - d * c' ≠ 0`. -/
def IsTangentLine (x₀ y₀ c d : F) : Prop :=
  W.IsDoublePoint x₀ y₀ ∧ (c ≠ 0 ∨ d ≠ 0) ∧
    C c * X 0 + C d * X 1 ∣ homogeneousComponent 2 (W.polynomialAt x₀ y₀)

/-- The intersection number at `(x₀, y₀)` of the line `c(X - x₀) + d(Y - y₀) = 0` with the
curve `f = 0`, defined as the order of vanishing at `t = 0` of the restriction
`f(x₀ + d t, y₀ - c t)` of `f` to the line.

Milne, *Elliptic Curves*, Chapter I, §1, defines the intersection number `I(P, L ∩ C)`
axiomatically (Proposition 1.8, p. 9, and p. 10) and computes it for a line `Y = f(X)` by
Lemma 1.11, p. 10, as the exponent of the power of `X` dividing the restriction; the
definition here is that restriction formula, parametrised by `t`. -/
noncomputable def lineIntersectionNumber (x₀ y₀ c d : F) : ℕ :=
  Polynomial.rootMultiplicity 0
    (aeval ![Polynomial.C x₀ + Polynomial.C d * Polynomial.X,
      Polynomial.C y₀ - Polynomial.C c * Polynomial.X] W.affineMvPolynomial)

/-- For a Weierstrass curve over an algebraically closed field `F`, `(x₀, y₀)` is a *node*: a
double point with two distinct tangent lines (Milne, *Elliptic Curves*, Chapter I, §1, p. 8: a
node is an ordinary double point, the tangent lines being taken over an algebraic closure). The
field is required to be algebraically closed, so that every tangent line is defined over it. -/
def IsNode [IsAlgClosed F] (x₀ y₀ : F) : Prop :=
  W.IsDoublePoint x₀ y₀ ∧ ∃ c d c' d' : F, W.IsTangentLine x₀ y₀ c d ∧
    W.IsTangentLine x₀ y₀ c' d' ∧ c * d' - d * c' ≠ 0

/-- For a Weierstrass curve over an algebraically closed field `F`, `(x₀, y₀)` is a *cusp*: a
double point with only one tangent line `L`, and `I(P, L ∩ C) = 3` (Milne, *Elliptic Curves*,
Chapter I, §1, Remark 1.12, p. 11). The field is required to be algebraically closed, so that
every tangent line is defined over it. -/
def IsCusp [IsAlgClosed F] (x₀ y₀ : F) : Prop :=
  W.IsDoublePoint x₀ y₀ ∧ ∃ c d : F, W.IsTangentLine x₀ y₀ c d ∧
    (∀ c' d' : F, W.IsTangentLine x₀ y₀ c' d' → c * d' - d * c' = 0) ∧
    W.lineIntersectionNumber x₀ y₀ c d = 3

lemma isDoublePoint_iff (x₀ y₀ : F) :
    W.IsDoublePoint x₀ y₀ ↔ W.toAffine.Equation x₀ y₀ ∧ ¬ W.toAffine.Nonsingular x₀ y₀ := by
  rw [IsDoublePoint, homogeneousComponent_zero_polynomialAt,
    homogeneousComponent_one_polynomialAt, homogeneousComponent_two_polynomialAt,
    Affine.nonsingular_iff, Affine.equation_iff, C_eq_zero, sub_eq_zero]
  have h2 : W.quadraticPart x₀ ≠ 0 := fun h => by
    simpa [quadraticPart] using congrArg (eval ![0, 1]) h
  constructor
  · rintro ⟨he, hl, -⟩
    have h0 := congrArg (eval ![1, 0]) hl
    have h1 := congrArg (eval ![0, 1]) hl
    simp only [map_add, map_mul, eval_C, eval_X, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one, mul_zero, add_zero, zero_add, map_zero] at h0 h1
    refine ⟨he, fun ⟨_, h⟩ => h.elim (fun h => h ?_) (fun h => h ?_)⟩
    · linear_combination h0
    · linear_combination h1
  · rintro ⟨he, hns⟩
    simp only [he, true_and, not_or, not_not] at hns
    refine ⟨he, ?_, h2⟩
    rw [hns.1, show 2 * y₀ + W.a₁ * x₀ + W.a₃ = 0 by linear_combination hns.2]
    simp

/-- At a singular point `(x₀, y₀)` of the affine Weierstrass curve, `c₄ = (b₂ + 12x₀)²`. -/
lemma c₄_eq_of_singular {x₀ y₀ : F} (he : W.toAffine.Equation x₀ y₀)
    (hns : ¬ W.toAffine.Nonsingular x₀ y₀) : W.c₄ = (W.b₂ + 12 * x₀) ^ 2 := by
  simp only [Affine.nonsingular_iff, he, true_and, not_or, not_not] at hns
  simp only [c₄, b₂, b₄]
  linear_combination 48 * hns.1 - 24 * W.a₁ * hns.2

/-- Two singular points of an affine Weierstrass curve over a field coincide. -/
lemma eq_of_singular {x₁ y₁ x₂ y₂ : F} (he₁ : W.toAffine.Equation x₁ y₁)
    (hns₁ : ¬ W.toAffine.Nonsingular x₁ y₁) (he₂ : W.toAffine.Equation x₂ y₂)
    (hns₂ : ¬ W.toAffine.Nonsingular x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  simp only [Affine.nonsingular_iff, he₁, he₂, true_and, not_or, not_not] at hns₁ hns₂
  rw [Affine.equation_iff] at he₁ he₂
  have hx : (x₂ - x₁) ^ 3 = 0 := by
    linear_combination 2 * he₂ - (x₂ - x₁) * hns₂.1 - (y₂ - y₁) * hns₂.2 - 2 * he₁ -
      (x₂ - x₁) * hns₁.1 - (y₂ - y₁) * hns₁.2
  have hx' : x₁ = x₂ := (sub_eq_zero.1 (pow_eq_zero_iff three_ne_zero |>.1 hx)).symm
  subst hx'
  have hy : (y₂ - y₁) ^ 2 = 0 := by
    linear_combination he₂ - he₁ - (y₂ - y₁) * hns₁.2
  exact ⟨rfl, (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hy)).symm⟩

end Local

section LineRestriction

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

lemma aeval_line_affineMvPolynomial (x₀ y₀ c d : F) :
    aeval ![Polynomial.C x₀ + Polynomial.C d * Polynomial.X,
      Polynomial.C y₀ - Polynomial.C c * Polynomial.X] W.affineMvPolynomial =
      Polynomial.C
          (y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) +
        Polynomial.C ((W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) * d -
          (2 * y₀ + W.a₁ * x₀ + W.a₃) * c) * Polynomial.X +
        Polynomial.C (c ^ 2 - W.a₁ * d * c - (3 * x₀ + W.a₂) * d ^ 2) * Polynomial.X ^ 2 -
        Polynomial.C (d ^ 3) * Polynomial.X ^ 3 := by
  simp only [affineMvPolynomial, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Polynomial.algebraMap_eq, map_ofNat, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private lemma quadraticPart_eq_mul {x₀ α : F} (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) :
    W.quadraticPart x₀ = (C (-α) * X 0 + C 1 * X 1) * (C (W.a₁ + α) * X 0 + C 1 * X 1) := by
  have h := congrArg (C : F → MvPolynomial (Fin 2) F) hα
  simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, map_zero] at h
  simp only [quadraticPart, map_add, map_neg, map_one, map_mul, map_ofNat]
  linear_combination (X 0 ^ 2) * h

private lemma exists_slope [IsAlgClosed F] (x₀ : F) :
    ∃ α : F, α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0 := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C W.a₁ * Polynomial.X +
      Polynomial.C (-(3 * x₀ + W.a₂))) (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
  refine ⟨α, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at hα
  linear_combination hα

/-- At a singular point of the affine Weierstrass curve over an algebraically closed field, if
`c₄ ≠ 0` the point is a node. -/
theorem isNode_of_singular [IsAlgClosed F] {x₀ y₀ : F} (he : W.toAffine.Equation x₀ y₀)
    (hns : ¬ W.toAffine.Nonsingular x₀ y₀) (hc : W.c₄ ≠ 0) : W.IsNode x₀ y₀ := by
  obtain ⟨α, hα⟩ := W.exists_slope x₀
  have hdisc : (2 * α + W.a₁) ^ 2 = W.b₂ + 12 * x₀ := by
    simp only [b₂]
    linear_combination 4 * hα
  have hne : 2 * α + W.a₁ ≠ 0 := by
    intro h
    rw [W.c₄_eq_of_singular he hns, ← hdisc, h] at hc
    simp at hc
  have hdp := (W.isDoublePoint_iff _ _).2 ⟨he, hns⟩
  refine ⟨hdp, -α, 1, W.a₁ + α, 1,
    ⟨hdp, Or.inr one_ne_zero, ?_⟩, ⟨hdp, Or.inr one_ne_zero, ?_⟩, ?_⟩
  · rw [homogeneousComponent_two_polynomialAt, W.quadraticPart_eq_mul hα]
    exact dvd_mul_right _ _
  · rw [homogeneousComponent_two_polynomialAt, W.quadraticPart_eq_mul hα]
    exact dvd_mul_left _ _
  · intro h
    exact hne (by linear_combination -h)

/-- At a singular point of the affine Weierstrass curve over an algebraically closed field, if
`c₄ = 0` the point is a cusp. -/
theorem isCusp_of_singular [IsAlgClosed F] {x₀ y₀ : F} (he : W.toAffine.Equation x₀ y₀)
    (hns : ¬ W.toAffine.Nonsingular x₀ y₀) (hc : W.c₄ = 0) : W.IsCusp x₀ y₀ := by
  obtain ⟨α, hα⟩ := W.exists_slope x₀
  have hdisc : (2 * α + W.a₁) ^ 2 = W.b₂ + 12 * x₀ := by
    simp only [b₂]
    linear_combination 4 * hα
  have h0 : 2 * α + W.a₁ = 0 := by
    rw [W.c₄_eq_of_singular he hns, ← hdisc, ← pow_mul] at hc
    exact pow_eq_zero_iff (by norm_num) |>.1 hc
  have he' := he
  rw [Affine.equation_iff] at he'
  have hns' := hns
  simp only [Affine.nonsingular_iff, he, true_and, not_or, not_not] at hns'
  have hdp := (W.isDoublePoint_iff _ _).2 ⟨he, hns⟩
  refine ⟨hdp, -α, 1, ⟨hdp, Or.inr one_ne_zero, ?_⟩, ?_, ?_⟩
  · rw [homogeneousComponent_two_polynomialAt, W.quadraticPart_eq_mul hα]
    exact dvd_mul_right _ _
  · rintro c' d' ⟨-, -, g, hg⟩
    rw [homogeneousComponent_two_polynomialAt] at hg
    have hq := congrArg (eval ![d', -c']) hg
    simp only [quadraticPart, map_add, map_sub, map_mul, map_pow, eval_C, eval_X,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hq
    have hsq : (c' + α * d') ^ 2 = 0 := by
      linear_combination hq + (d' * (c' + α * d')) * h0 - d' ^ 2 * hα
    have := pow_eq_zero_iff two_ne_zero |>.1 hsq
    linear_combination -this
  · rw [lineIntersectionNumber, aeval_line_affineMvPolynomial]
    have e0 : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
        (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) = 0 := by linear_combination he'
    have e1 : (W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) * 1 -
        (2 * y₀ + W.a₁ * x₀ + W.a₃) * -α = 0 := by
      linear_combination hns'.1 + α * hns'.2
    have e2 : (-α) ^ 2 - W.a₁ * 1 * -α - (3 * x₀ + W.a₂) * 1 ^ 2 = 0 := by
      linear_combination hα
    rw [e0, e1, e2]
    simp only [map_zero, zero_mul, zero_add, one_pow, map_one, one_mul, zero_sub]
    rw [show (-Polynomial.X ^ 3 : Polynomial F) =
        Polynomial.C (-1) * (Polynomial.X - Polynomial.C 0) ^ 3 by simp,
      Polynomial.rootMultiplicity_mul (by simp), Polynomial.rootMultiplicity_C,
      Polynomial.rootMultiplicity_X_sub_C_pow, zero_add]

end LineRestriction

section Existence

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private lemma exists_singular_aux (h2 : (2 : F) ≠ 0) {u v : F} (hb₂ : W.b₂ = -4 * (2 * u + v))
    (hb₄ : 2 * W.b₄ = 4 * (u ^ 2 + 2 * u * v)) (hb₆ : W.b₆ = -4 * (u ^ 2 * v)) :
    ∃ x y : F, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have h4 : (4 : F) ≠ 0 := by
    have := mul_ne_zero h2 h2
    norm_num at this
    exact this
  obtain ⟨y, hy⟩ : ∃ y : F, 2 * y = -(W.a₁ * u + W.a₃) :=
    ⟨-(W.a₁ * u + W.a₃) / 2, by field_simp⟩
  simp only [b₂, b₄, b₆] at hb₂ hb₄ hb₆
  have he : W.toAffine.Equation u y := by
    rw [Affine.equation_iff]
    apply mul_left_cancel₀ h4
    linear_combination (2 * y + W.a₁ * u + W.a₃) * hy - u ^ 2 * hb₂ - u * hb₄ - hb₆
  refine ⟨u, y, he, ?_⟩
  simp only [Affine.nonsingular_iff, he, true_and, not_or, not_not]
  refine ⟨?_, by linear_combination hy⟩
  apply mul_left_cancel₀ h4
  linear_combination 2 * W.a₁ * hy - 2 * u * hb₂ - hb₄

/-- If `Δ = 0`, an affine Weierstrass curve over an algebraically closed field (of any
characteristic) has a singular point. -/
theorem exists_singular_of_Δ_eq_zero [IsAlgClosed F] (hΔ : W.Δ = 0) :
    ∃ x y : F, W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  by_cases h2 : (2 : F) = 0
  · obtain ⟨a₁, a₂, a₃, a₄, a₆⟩ := W
    simp only [Δ, b₂, b₄, b₆, b₈] at hΔ
    by_cases ha₁ : a₁ = 0
    · subst ha₁
      have ha₃ : a₃ = 0 := by
        have h : a₃ ^ 4 = 0 := by
          linear_combination hΔ +
            (8 * a₂ ^ 3 * a₃ ^ 2 + 32 * a₂ ^ 3 * a₆ - 8 * a₂ ^ 2 * a₄ ^ 2 -
              36 * a₂ * a₃ ^ 2 * a₄ - 144 * a₂ * a₄ * a₆ + 14 * a₃ ^ 4 + 108 * a₃ ^ 2 * a₆ +
              32 * a₄ ^ 3 + 216 * a₆ ^ 2) * h2
        exact pow_eq_zero_iff (by norm_num) |>.1 h
      subst ha₃
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (-a₄) two_pos
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆) two_pos
      have he : Affine.Equation ⟨0, a₂, 0, a₄, a₆⟩ x y := by
        rw [Affine.equation_iff]
        linear_combination hy
      refine ⟨x, y, he, ?_⟩
      simp only [Affine.nonsingular_iff, he, true_and, not_or, not_not]
      exact ⟨by linear_combination -hx - (x ^ 2 + a₂ * x) * h2, by linear_combination y * h2⟩
    · obtain ⟨x, rfl⟩ : ∃ x, a₃ = a₁ * x := ⟨a₃ / a₁, by field_simp⟩
      obtain ⟨y, rfl⟩ : ∃ y, a₄ = a₁ * y - 3 * x ^ 2 - 2 * a₂ * x :=
        ⟨(a₄ + 3 * x ^ 2 + 2 * a₂ * x) / a₁, by field_simp; ring⟩
      have he : Affine.Equation ⟨a₁, a₂, a₁ * x, a₁ * y - 3 * x ^ 2 - 2 * a₂ * x, a₆⟩ x y := by
        rw [Affine.equation_iff]
        have h : a₁ ^ 6 * (y ^ 2 + a₁ * x * y + a₁ * x * y -
            (x ^ 3 + a₂ * x ^ 2 + (a₁ * y - 3 * x ^ 2 - 2 * a₂ * x) * x + a₆)) = 0 := by
          linear_combination hΔ +
            (2 * a₁ ^ 6 * a₂ * x ^ 2 + 2 * a₁ ^ 6 * x ^ 3 - 2 * a₁ ^ 5 * a₂ * x * y +
              18 * a₁ ^ 5 * x ^ 2 * y + 10 * a₁ ^ 4 * a₂ ^ 2 * x ^ 2 + 6 * a₁ ^ 4 * a₂ * a₆ -
              42 * a₁ ^ 4 * a₂ * x ^ 3 - 4 * a₁ ^ 4 * a₂ * y ^ 2 - 18 * a₁ ^ 4 * a₆ * x -
              36 * a₁ ^ 4 * x ^ 4 + 48 * a₁ ^ 4 * x * y ^ 2 + 8 * a₁ ^ 3 * a₂ ^ 2 * x * y -
              204 * a₁ ^ 3 * a₂ * x ^ 2 * y - 36 * a₁ ^ 3 * a₆ * y - 288 * a₁ ^ 3 * x ^ 3 * y +
              32 * a₁ ^ 3 * y ^ 3 + 8 * a₁ ^ 2 * a₂ ^ 3 * x ^ 2 + 24 * a₁ ^ 2 * a₂ ^ 2 * a₆ +
              240 * a₁ ^ 2 * a₂ ^ 2 * x ^ 3 - 8 * a₁ ^ 2 * a₂ ^ 2 * y ^ 2 +
              648 * a₁ ^ 2 * a₂ * x ^ 4 - 192 * a₁ ^ 2 * a₂ * x * y ^ 2 +
              216 * a₁ ^ 2 * a₆ * x ^ 2 + 432 * a₁ ^ 2 * x ^ 5 - 288 * a₁ ^ 2 * x ^ 2 * y ^ 2 +
              32 * a₁ * a₂ ^ 3 * x * y + 432 * a₁ * a₂ ^ 2 * x ^ 2 * y - 144 * a₁ * a₂ * a₆ * y +
              1152 * a₁ * a₂ * x ^ 3 * y + 864 * a₁ * x ^ 4 * y - 32 * a₂ ^ 4 * x ^ 2 +
              32 * a₂ ^ 3 * a₆ - 352 * a₂ ^ 3 * x ^ 3 + 288 * a₂ ^ 2 * a₆ * x -
              1224 * a₂ ^ 2 * x ^ 4 + 432 * a₂ * a₆ * x ^ 2 - 1728 * a₂ * x ^ 5 + 216 * a₆ ^ 2 -
              864 * x ^ 6) * h2
        exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left (pow_ne_zero 6 ha₁))
      refine ⟨x, y, he, ?_⟩
      simp only [Affine.nonsingular_iff, he, true_and, not_or, not_not]
      exact ⟨by ring, by linear_combination (y + a₁ * x) * h2⟩
  · have ha : W.twoTorsionPolynomial.a ≠ 0 := by
      simp only [twoTorsionPolynomial]
      have := mul_ne_zero h2 h2
      norm_num at this
      exact this
    obtain ⟨r, s, t, h3⟩ := (Cubic.splits_iff_roots_eq_three (φ := RingHom.id F) ha).1
      (by rw [Polynomial.map_id]; exact IsAlgClosed.splits _)
    have hd : ¬ (r ≠ s ∧ r ≠ t ∧ s ≠ t) := fun h =>
      (Cubic.discr_ne_zero_iff_roots_ne ha h3).2 h
        (by rw [twoTorsionPolynomial_discr, hΔ, mul_zero])
    have hb := Cubic.b_eq_three_roots ha h3
    have hc := Cubic.c_eq_three_roots ha h3
    have hd' := Cubic.d_eq_three_roots ha h3
    simp only [twoTorsionPolynomial, RingHom.id_apply] at hb hc hd'
    by_cases hrs : r = s
    · subst hrs
      exact W.exists_singular_aux h2 (u := r) (v := t) (by linear_combination hb)
        (by linear_combination hc) (by linear_combination hd')
    by_cases hrt : r = t
    · subst hrt
      exact W.exists_singular_aux h2 (u := r) (v := s) (by linear_combination hb)
        (by linear_combination hc) (by linear_combination hd')
    have hst : s = t := by
      by_contra hst
      exact hd ⟨hrs, hrt, hst⟩
    subst hst
    exact W.exists_singular_aux h2 (u := s) (v := r) (by linear_combination hb)
      (by linear_combination hc) (by linear_combination hd')

end Existence

section Projective

open scoped WeierstrassCurve.Projective

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- `P = (P 0 : P 1 : P 2)` is a singular point of the projective Weierstrass cubic
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`: `P ≠ 0`, `P` lies on the cubic, and `P` is
not a nonsingular point in the sense of `WeierstrassCurve.Projective.Nonsingular`. -/
def IsSingularPoint (P : Fin 3 → F) : Prop :=
  P ≠ 0 ∧ W.toProjective.Equation P ∧ ¬ W.toProjective.Nonsingular P

/-- For a Weierstrass curve over an algebraically closed field `F`, `P` is a node of the
projective cubic: `P` lies in the affine chart `Z ≠ 0` and
`(P 0 / P 2, P 1 / P 2)` is a node of the affine curve (as in Milne, *Elliptic Curves*,
Chapter II, §3, p. 57, where nodes and cusps of plane cubics are read off in an affine chart). -/
def IsProjectiveNode [IsAlgClosed F] (P : Fin 3 → F) : Prop :=
  P 2 ≠ 0 ∧ W.IsNode (P 0 / P 2) (P 1 / P 2)

/-- For a Weierstrass curve over an algebraically closed field `F`, `P` is a cusp of the
projective cubic: `P` lies in the affine chart `Z ≠ 0` and
`(P 0 / P 2, P 1 / P 2)` is a cusp of the affine curve (as in Milne, *Elliptic Curves*,
Chapter II, §3, p. 57). -/
def IsProjectiveCusp [IsAlgClosed F] (P : Fin 3 → F) : Prop :=
  P 2 ≠ 0 ∧ W.IsCusp (P 0 / P 2) (P 1 / P 2)

/-- A singular point of the projective cubic is not on the line `Z = 0`. -/
lemma IsSingularPoint.Z_ne_zero {P : Fin 3 → F} (h : W.IsSingularPoint P) : P 2 ≠ 0 := by
  intro hz
  obtain ⟨hP, he, hns⟩ := h
  have hx : P 0 = 0 :=
    pow_eq_zero_iff three_ne_zero |>.1 ((Projective.equation_of_Z_eq_zero hz).1 he)
  have hy : P 1 ≠ 0 := fun hy => hP (funext fun i => by fin_cases i <;> simp [hx, hy, hz])
  exact hns ((Projective.nonsingular_of_Z_eq_zero hz).2 ⟨he, Or.inr (by simp [hx, hy])⟩)

lemma isSingularPoint_iff_of_Z_ne_zero {P : Fin 3 → F} (hz : P 2 ≠ 0) :
    W.IsSingularPoint P ↔
      W.toAffine.Equation (P 0 / P 2) (P 1 / P 2) ∧
        ¬ W.toAffine.Nonsingular (P 0 / P 2) (P 1 / P 2) := by
  have hP : P ≠ 0 := fun h => hz (by simp [h])
  rw [IsSingularPoint, Projective.equation_of_Z_ne_zero hz, Projective.nonsingular_of_Z_ne_zero hz]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩

lemma isSingularPoint_some (x y : F) :
    W.IsSingularPoint ![x, y, 1] ↔ W.toAffine.Equation x y ∧ ¬ W.toAffine.Nonsingular x y := by
  have hP : (![x, y, 1] : Fin 3 → F) ≠ 0 := fun h => one_ne_zero (congrFun h 2)
  rw [IsSingularPoint, Projective.equation_some, Projective.nonsingular_some]
  exact ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩

/-- If `Δ ≠ 0`, every point of the projective cubic is nonsingular (over any field). -/
theorem nonsingular_of_Δ_ne_zero (hΔ : W.Δ ≠ 0) {P : Fin 3 → F} (hP : P ≠ 0)
    (he : W.toProjective.Equation P) : W.toProjective.Nonsingular P := by
  by_contra hns
  have hs : W.IsSingularPoint P := ⟨hP, he, hns⟩
  rw [W.isSingularPoint_iff_of_Z_ne_zero (hs.Z_ne_zero W)] at hs
  exact hs.2 ((Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 hs.1)

/-- **Singular points of Weierstrass cubics, part 1.** Over an algebraically closed field, the
projective Weierstrass cubic is nonsingular if and only if `Δ ≠ 0`. -/
theorem nonsingular_iff_Δ_ne_zero [IsAlgClosed F] :
    (∀ P : Fin 3 → F, P ≠ 0 → W.toProjective.Equation P → W.toProjective.Nonsingular P) ↔
      W.Δ ≠ 0 := by
  refine ⟨fun h hΔ => ?_, fun hΔ _ hP he => W.nonsingular_of_Δ_ne_zero hΔ hP he⟩
  obtain ⟨x, y, he, hns⟩ := W.exists_singular_of_Δ_eq_zero hΔ
  have hs := (W.isSingularPoint_some x y).2 ⟨he, hns⟩
  exact hs.2.2 (h _ hs.1 hs.2.1)

/-- **Singular points of Weierstrass cubics, part 2 (existence, uniqueness, position).** Over
an algebraically closed field, if `Δ = 0` the projective Weierstrass cubic has exactly one
singular point up to scaling, and it is not `(0 : 1 : 0)`. -/
theorem existsUnique_isSingularPoint [IsAlgClosed F] (hΔ : W.Δ = 0) :
    ∃ S : Fin 3 → F, W.IsSingularPoint S ∧ (∀ P, W.IsSingularPoint P → P ≈ S) ∧
      ¬ S ≈ ![0, 1, 0] := by
  obtain ⟨x, y, he, hns⟩ := W.exists_singular_of_Δ_eq_zero hΔ
  have hs := (W.isSingularPoint_some x y).2 ⟨he, hns⟩
  refine ⟨![x, y, 1], hs, fun P hP => ?_, fun h => ?_⟩
  · have hz := hP.Z_ne_zero W
    rw [W.isSingularPoint_iff_of_Z_ne_zero hz] at hP
    obtain ⟨h1, h2⟩ := W.eq_of_singular hP.1 hP.2 he hns
    rw [← h1, ← h2]
    exact Projective.equiv_some_of_Z_ne_zero hz
  · exact hs.2.2 ((Projective.nonsingular_of_equiv h).2 Projective.nonsingular_zero)

/-- **Singular points of Weierstrass cubics, part 2 (type).** Over an algebraically closed
field, a singular point of the projective Weierstrass cubic is a node if `c₄ ≠ 0` and a cusp if
`c₄ = 0`. -/
theorem isProjectiveNode_and_isProjectiveCusp [IsAlgClosed F] {P : Fin 3 → F}
    (hP : W.IsSingularPoint P) :
    (W.c₄ ≠ 0 → W.IsProjectiveNode P) ∧ (W.c₄ = 0 → W.IsProjectiveCusp P) := by
  have hz := hP.Z_ne_zero W
  rw [W.isSingularPoint_iff_of_Z_ne_zero hz] at hP
  exact ⟨fun hc => ⟨hz, W.isNode_of_singular hP.1 hP.2 hc⟩,
    fun hc => ⟨hz, W.isCusp_of_singular hP.1 hP.2 hc⟩⟩

end Projective

section BaseChange

open scoped WeierstrassCurve.Projective

variable {F K : Type*} [Field F] [Field K] [IsAlgClosed K] [Algebra F K]
  (W : WeierstrassCurve F)

/-- **Singular points of Weierstrass cubics, part 1, over `F̄`.** Let `W` be a Weierstrass
curve over a field `F` and `K` an algebraically closed field containing `F` (e.g. an algebraic
closure of `F`). The projective cubic `C_K` is nonsingular if and only if `Δ ≠ 0`.

Milne, *Elliptic Curves*, 2nd ed., Chapter II, Theorem 2.4(a), p. 52. -/
theorem map_nonsingular_iff_Δ_ne_zero :
    (∀ P : Fin 3 → K, P ≠ 0 → (W.map (algebraMap F K)).toProjective.Equation P →
      (W.map (algebraMap F K)).toProjective.Nonsingular P) ↔ W.Δ ≠ 0 := by
  rw [nonsingular_iff_Δ_ne_zero, map_Δ, map_ne_zero]

/-- **Singular points of Weierstrass cubics, part 2, over `F̄`.** Let `W` be a Weierstrass
curve over a field `F` with `Δ = 0`, and `K` an algebraically closed field containing `F`.
Then `C_K` has exactly one singular point `S` (up to scaling), `S ≠ (0 : 1 : 0)`, and `S` is a
node if `c₄ ≠ 0` and a cusp if `c₄ = 0`.

Nodes and cusps are in the sense of Milne, *Elliptic Curves*, 2nd ed., Chapter I, §1, p. 8
(multiplicity, tangent lines, a node is an ordinary double point) and Remark 1.12, p. 11
(cusps). The statement is Milne, Chapter II, §3, pp. 57–59 (in particular p. 59: "the
singularity is cusp if `c4 = 0` and a node if `c4 ≠ 0`", citing Tate 1974, p. 182), and
p. 58 ("the point `(0 : 1 : 0)` is always nonsingular"). -/
theorem existsUnique_isSingularPoint_map (hΔ : W.Δ = 0) :
    ∃ S : Fin 3 → K, (W.map (algebraMap F K)).IsSingularPoint S ∧
      (∀ P, (W.map (algebraMap F K)).IsSingularPoint P → P ≈ S) ∧ ¬ S ≈ ![0, 1, 0] ∧
      (W.c₄ ≠ 0 → (W.map (algebraMap F K)).IsProjectiveNode S) ∧
      (W.c₄ = 0 → (W.map (algebraMap F K)).IsProjectiveCusp S) := by
  have hΔ' : (W.map (algebraMap F K)).Δ = 0 := by rw [map_Δ, hΔ, map_zero]
  obtain ⟨S, hS, huniq, hinf⟩ := (W.map (algebraMap F K)).existsUnique_isSingularPoint hΔ'
  have h := (W.map (algebraMap F K)).isProjectiveNode_and_isProjectiveCusp hS
  rw [map_c₄, map_ne_zero, map_eq_zero_iff _ (algebraMap F K).injective] at h
  exact ⟨S, hS, huniq, hinf, h.1, h.2⟩

/-- **Singular points of Weierstrass cubics.** Let `F` be a field with algebraic closure `F̄`
(more generally, let `K` be any algebraically closed field containing `F`), and let
`C ⊂ ℙ²` be the plane cubic
`Y²Z + a₁XYZ + a₃YZ² = X³ + a₂X²Z + a₄XZ² + a₆Z³`, `a₁, …, a₆ ∈ F`, with the quantities `c₄`
and `Δ` of `W`. Then

1. `C` is nonsingular over `K` if and only if `Δ ≠ 0`;
2. if `Δ = 0`, then `C_K` has exactly one singular point `S` (up to scaling), and
   `S ≠ (0 : 1 : 0)`; it is a node if `c₄ ≠ 0` and a cusp if `c₄ = 0`.

A singular point is a node if it is a double point with two distinct tangent lines
(`WeierstrassCurve.IsNode`), and a cusp if it is a double point with a single tangent line `L`
and the intersection number of `L` and the curve at the point is `3`
(`WeierstrassCurve.IsCusp`, with the intersection number of a line computed by restriction,
`WeierstrassCurve.lineIntersectionNumber`).

Source: J. S. Milne, *Elliptic Curves*, 2nd ed., World Scientific, 2021, author's version
<https://www.jmilne.org/math/Books/EC2.pdf>: Chapter I, §1, p. 8 (multiplicity, tangent lines,
nodes) and Remark 1.12, p. 11 (cusps); Chapter II, Theorem 2.4(a), p. 52 (the curve is
nonsingular if and only if `Δ ≠ 0`); Chapter II, §3, pp. 57–59 (p. 58: "the point `(0 : 1 : 0)`
is always nonsingular"; p. 59: "the singularity is cusp if `c4 = 0` and a node if `c4 ≠ 0`",
citing J. Tate, Invent. Math. 23 (1974), p. 182). -/
theorem singular_points_of_weierstrass_cubic :
    ((∀ P : Fin 3 → K, P ≠ 0 → (W.map (algebraMap F K)).toProjective.Equation P →
      (W.map (algebraMap F K)).toProjective.Nonsingular P) ↔ W.Δ ≠ 0) ∧
    (W.Δ = 0 → ∃ S : Fin 3 → K, (W.map (algebraMap F K)).IsSingularPoint S ∧
      (∀ P, (W.map (algebraMap F K)).IsSingularPoint P → P ≈ S) ∧ ¬ S ≈ ![0, 1, 0] ∧
      (W.c₄ ≠ 0 → (W.map (algebraMap F K)).IsProjectiveNode S) ∧
      (W.c₄ = 0 → (W.map (algebraMap F K)).IsProjectiveCusp S)) :=
  ⟨W.map_nonsingular_iff_Δ_ne_zero, W.existsUnique_isSingularPoint_map⟩

end BaseChange

end WeierstrassCurve
