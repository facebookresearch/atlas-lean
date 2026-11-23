/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.Ideal.Basic

@[expose] public section

set_option autoImplicit false

noncomputable section

/-! # Translated tangent spaces (ATLAS ArithmeticGeometry Definition 17.1)

This module formalizes translated tangent vectors at a point `P`:
the total derivative of a polynomial along a direction `v`,
its linearization, and the tangent spaces of a hypersurface and of an ideal.
-/

namespace MvPolynomial

variable {k : Type*} [Field k] {n : Nat}

/-- **Total derivative at a point.** For a field $k$, a polynomial $f \in k[x_1, \dots, x_n]$ and
$P, v \in k^n$, the total derivative of $f$ at $P$ along the translated direction $v$ is
$\sum_{i=1}^n \frac{\partial f}{\partial x_i}(P)\, v_i \in k$, where
$\frac{\partial f}{\partial x_i}$ is the formal partial derivative. -/
def totalDerivativeAt (f : MvPolynomial (Fin n) k) (P v : Fin n → k) : k :=
  ∑ i : Fin n, MvPolynomial.eval P (MvPolynomial.pderiv i f) * v i

/-- **Total derivative as a linear map.** For a field $k$, a polynomial $f \in k[x_1, \dots, x_n]$
and a point $P \in k^n$, this is the $k$-linear map $k^n \to k$ sending $v$ to the total derivative
of $f$ at $P$ along $v$, namely $\sum_{i=1}^n \frac{\partial f}{\partial x_i}(P)\, v_i$. -/
def totalDerivativeAtLin (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    (Fin n → k) →ₗ[k] k where
  toFun := totalDerivativeAt f P
  map_add' x y := by
    simp only [totalDerivativeAt, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [totalDerivativeAt, Pi.smul_apply, smul_eq_mul, mul_left_comm,
      ← Finset.mul_sum, RingHom.id_apply]

/-- **Tangent space of a hypersurface.** For a field $k$, a polynomial $f \in k[x_1, \dots, x_n]$
and a point $P \in k^n$, the tangent space of the hypersurface $f = 0$ at $P$ is the kernel of the
total derivative of $f$ at $P$, viewed as a $k$-linear map $k^n \to k$: the subspace of vectors
$v \in k^n$ with $\sum_{i=1}^n \frac{\partial f}{\partial x_i}(P)\, v_i = 0$. The point $P$ is not
required to satisfy $f(P) = 0$. -/
def tangentSpacePoly (f : MvPolynomial (Fin n) k) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  LinearMap.ker (totalDerivativeAtLin f P)

/-- **Tangent space of an ideal.** For a field $k$, an ideal $I$ of $k[x_1, \dots, x_n]$ and a
point $P \in k^n$, the tangent space of $I$ at $P$ is the $k$-linear subspace of $k^n$ obtained
as the intersection, over all $f \in I$, of the tangent spaces at $P$ of the hypersurfaces
$f = 0$. The point $P$ is not required to be a common zero of $I$. -/
def tangentSpaceIdeal (I : Ideal (MvPolynomial (Fin n) k)) (P : Fin n → k) :
    Submodule k (Fin n → k) :=
  ⨅ f ∈ I, tangentSpacePoly f P

/-- **Evaluating the total derivative linear map.** For a field $k$, a polynomial
$f \in k[x_1, \dots, x_n]$ and $P, v \in k^n$, the total derivative of $f$ at $P$, viewed as a
$k$-linear map $k^n \to k$, sends $v$ to the total derivative of $f$ at $P$ along $v$. -/
@[simp]
theorem totalDerivativeAtLin_apply (f : MvPolynomial (Fin n) k) (P : Fin n → k)
    (v : Fin n → k) :
    totalDerivativeAtLin f P v = totalDerivativeAt f P v :=
  rfl

/-- **Membership in the tangent space of a hypersurface.** Let $k$ be a field,
$f \in k[x_1, \dots, x_n]$, and $P, v \in k^n$. Then $v$ lies in the tangent space of the
hypersurface $f = 0$ at $P$ if and only if the total derivative of $f$ at $P$ along $v$ is zero. -/
@[simp]
theorem mem_tangentSpacePoly (f : MvPolynomial (Fin n) k) (P : Fin n → k)
    (v : Fin n → k) :
    v ∈ tangentSpacePoly f P ↔ totalDerivativeAt f P v = 0 :=
  LinearMap.mem_ker

/-- **Membership in the tangent space of an ideal.** Let $k$ be a field, $I$ an ideal of
$k[x_1, \dots, x_n]$, and $P, v \in k^n$. Then $v$ lies in the tangent space of $I$ at $P$ if and
only if, for every $f \in I$, the total derivative of $f$ at $P$ along $v$ is zero. -/
theorem mem_tangentSpaceIdeal (I : Ideal (MvPolynomial (Fin n) k)) (P : Fin n → k)
    (v : Fin n → k) :
    v ∈ tangentSpaceIdeal I P ↔ ∀ f ∈ I, totalDerivativeAt f P v = 0 := by
  simp [tangentSpaceIdeal, mem_tangentSpacePoly, Submodule.mem_iInf]

end MvPolynomial
