/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.Curve.Divisor
public import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Evaluation of curve divisors

This file defines the generic algebraic evaluation of a divisor against a function into a
commutative group. It does not impose rational-function or disjoint-support hypotheses.
-/

@[expose] public section

namespace CurveDivisor

variable {C G : Type*} [CommGroup G]

/-- **Evaluation of divisors as a group homomorphism.** For a commutative group $G$ and a
function $f : C \to G$, this is the monoid homomorphism from the group of divisors on $C$,
written multiplicatively, to $G$ that sends a divisor $D$ to the finite product
$\prod_{P \in \operatorname{supp} D} f(P)^{D(P)}$. -/
noncomputable def evalMonoidHom (f : C → G) : Multiplicative (CurveDivisor C) →* G where
  toFun D := D.toAdd.prod fun P n ↦ f P ^ n
  map_one' := by simp
  map_mul' D₁ D₂ :=
    Finsupp.prod_add_index' (fun P ↦ zpow_zero (f P))
      (fun P n₁ n₂ ↦ zpow_add (f P) n₁ n₂)

/-- **Evaluation of a divisor against a function.** For a commutative group $G$, a function
$f : C \to G$ and a divisor $D$ on $C$, the evaluation of $D$ against $f$ is the element
$f(D) = \prod_{P \in \operatorname{supp} D} f(P)^{D(P)}$ of $G$. -/
noncomputable def eval (f : C → G) (D : CurveDivisor C) : G :=
  evalMonoidHom f (Multiplicative.ofAdd D)

/-- **Evaluation is a product over the support.** For a commutative group $G$, every function
$f : C \to G$ and every divisor $D$ on $C$, the evaluation of $D$ against $f$ equals
$\prod_{P \in \operatorname{supp} D} f(P)^{D(P)}$, the product over the points in the support
of $D$. -/
theorem eval_eq_prod (f : C → G) (D : CurveDivisor C) :
    eval f D = D.prod (fun P n ↦ f P ^ n) :=
  rfl

/-- **The zero divisor evaluates to one.** For a commutative group $G$ and every function
$f : C \to G$, the evaluation of the zero divisor on $C$ against $f$ is the identity element
$1$ of $G$. -/
@[simp]
theorem eval_zero (f : C → G) : eval f (0 : CurveDivisor C) = 1 := by
  simp [eval]

/-- **Evaluation of a one-point divisor.** For a commutative group $G$, every function
$f : C \to G$, every point $P \in C$ and every integer $n$, the divisor $n \cdot P$, with
coefficient $n$ at $P$ and $0$ elsewhere, evaluates against $f$ to $f(P)^n$. -/
@[simp]
theorem eval_single (f : C → G) (P : C) (n : ℤ) :
    eval f (Finsupp.single P n) = f P ^ n := by
  rw [eval_eq_prod]
  exact Finsupp.prod_single_index (zpow_zero (f P))

/-- **Evaluation is multiplicative.** For a commutative group $G$, every function
$f : C \to G$ and all divisors $D_1, D_2$ on $C$, writing $f(D)$ for the evaluation of a
divisor $D$ against $f$, we have $f(D_1 + D_2) = f(D_1) \, f(D_2)$. -/
@[simp]
theorem eval_add (f : C → G) (D₁ D₂ : CurveDivisor C) :
    eval f (D₁ + D₂) = eval f D₁ * eval f D₂ := by
  change evalMonoidHom f (Multiplicative.ofAdd D₁ * Multiplicative.ofAdd D₂) =
    evalMonoidHom f (Multiplicative.ofAdd D₁) * evalMonoidHom f (Multiplicative.ofAdd D₂)
  exact map_mul _ _ _

/-- **Evaluation of an integer multiple.** For a commutative group $G$, every function
$f : C \to G$, every integer $n$ and every divisor $D$ on $C$, writing $f(D)$ for the
evaluation of $D$ against $f$, we have $f(nD) = f(D)^n$. -/
@[simp]
theorem eval_zsmul (f : C → G) (n : ℤ) (D : CurveDivisor C) :
    eval f (n • D) = eval f D ^ n := by
  change evalMonoidHom f (Multiplicative.ofAdd D ^ n) =
    evalMonoidHom f (Multiplicative.ofAdd D) ^ n
  exact map_zpow _ _ _

end CurveDivisor
