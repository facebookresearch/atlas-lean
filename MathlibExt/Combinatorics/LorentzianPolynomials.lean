/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Combinatorics/LorentzianPolynomials.lean` (leanprover/lean-eval, revision 38361be):
the definitions and topology instance from the Annals Challenge formalization of
Brändén and Huh's *Lorentzian polynomials*, submitted to lean-eval by Justus Springer.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Copyright 2026 Lean FRO, LLC.
Authors: Justus Springer (lean-eval submission).

ATLAS placed these definitions in their present namespace and reused the general M-convexity
predicate. They moved here from `WantedExt/Combinatorics/LorentzianPolynomialsWanted.lean`.
-/

module

public import MathlibExt.Combinatorics.Matroid.MConvex
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Lorentzian polynomials

This module defines the sets of strictly Lorentzian and Lorentzian homogeneous polynomials
following Brändén and Huh, *Lorentzian polynomials*.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.LorentzianPolynomialsWanted

set_option autoImplicit false

namespace LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane

/-- **Homogeneous polynomials of degree $d$.** For natural numbers $n$ and $d$, $H^d_n$ denotes
the space of homogeneous polynomials of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$, including the
zero polynomial. -/
def H (n d : ℕ) : Type := homogeneousSubmodule (Fin n) ℝ d

/-- See start of Section 2: We define a topology on `H n d` using the Euclidean norm
for the coefficients. Since `homogeneousSubmodule (Fin n) ℝ d` is a finite-dimensional
`ℝ`-vector space, this coincides with its module topology over `ℝ`. -/
noncomputable instance {n d : ℕ} : TopologicalSpace (H n d) :=
  moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d)

/-- **Homogeneous polynomials with positive coefficients.** $P^d_n$ is the set of homogeneous
polynomials $f$ of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ such that the coefficient in $f$ of
every monomial of degree $d$ is strictly positive. -/
abbrev P (n d : ℕ) : Set (H n d) :=
  { f | ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < f.1.coeff m }

/-- **Hessian of a quadratic form.** For a homogeneous polynomial $f$ of degree $2$ in
$\mathbb{R}[w_1, \dots, w_n]$, its Hessian is the real $n \times n$ matrix $\mathcal{H}_f$ of second
partial derivatives of $f$: the diagonal entry $(i, i)$ is twice the coefficient of $w_i^2$ in $f$,
and for $i \ne j$ the entry $(i, j)$ is the coefficient of $w_i w_j$ in $f$. -/
noncomputable def H.hessian {n : ℕ} (f : H n 2) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if i = j then
      2 * f.1.coeff (single i 2)
    else
      f.1.coeff (single i 1 + single j 1)

/-- **Strictly Lorentzian polynomials.** For natural numbers $n$ and $d$, the set $\mathring{L}^d_n$
of strictly Lorentzian polynomials of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ is defined by
recursion on $d$. Let $P^d_n$ be the set of homogeneous polynomials of degree $d$ in which every
monomial of degree $d$ has a strictly positive coefficient, and let $\partial_i$ be the partial
derivative with respect to $w_i$. Then $\mathring{L}^0_n = P^0_n$ and $\mathring{L}^1_n = P^1_n$;
$\mathring{L}^2_n$ is the set of $f \in P^2_n$ whose Hessian matrix
$(\partial_i \partial_j f)_{i,j}$ is invertible and has exactly one positive eigenvalue, counted
with multiplicity; and for $d \ge 3$, $\mathring{L}^d_n$ is the set of $f \in P^d_n$ such that
$\partial_i f \in \mathring{L}^{d-1}_n$ for every $i$. -/
def Ŀ (n d : ℕ) : Set (H n d) := match d with
  | 0 => P n 0
  | 1 => P n 1
  | 2 => { f ∈ P n 2 | IsUnit f.hessian ∧ (f.hessian.charpoly.roots.filter (0 < ·)).card = 1 }
  | d + 3 => { f ∈ P n (d + 3) | ∀ i, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ Ŀ n (d + 2) }

/-- **M-convex sets.** A subset $J \subseteq \mathbb{N}^n$ is M-convex if for all
$\alpha, \beta \in J$ and every index $i$ with $\alpha_i > \beta_i$ there is an index $j$ with
$\alpha_j < \beta_j$ and $\alpha - e_i + e_j \in J$, where $e_1, \dots, e_n$ are the standard unit
vectors of $\mathbb{N}^n$. -/
def IsMConvex {n : ℕ} (J : Set (Fin n →₀ ℕ)) : Prop :=
  MathlibExt.Combinatorics.Matroid.MConvex.IsMConvex J

/-- **Homogeneous polynomials with M-convex support.** $M^d_n$ is the set of homogeneous
polynomials $f$ of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ whose coefficients are all
nonnegative and whose support, the set of exponent vectors $\alpha \in \mathbb{N}^n$ of the
monomials with nonzero coefficient in $f$, is M-convex. -/
abbrev M (n d : ℕ) : Set (H n d) :=
  { f | IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) ∧ ∀ m, 0 ≤ f.1.coeff m }

/-- **Stable polynomials.** A polynomial $f \in \mathbb{R}[w_1, \dots, w_n]$ is stable if either
$f$ is the zero polynomial or $f(z_1, \dots, z_n) \ne 0$ for all $z_1, \dots, z_n$ in the open upper
half plane $\mathbb{H} = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$. -/
def IsStable {n : ℕ} (f : MvPolynomial (Fin n) ℝ) : Prop :=
  f = 0 ∨ ∀ z : Fin n → ℍ, aeval (((↑) : ℍ → ℂ) ∘ z) f ≠ 0

/-- **Stable homogeneous polynomials with nonnegative coefficients.** $S^d_n$ is the set of
homogeneous polynomials $f$ of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ whose coefficients are
all nonnegative and that are stable: either $f$ is the zero polynomial or $f$ has no zero in
$\mathbb{H}^n$, where $\mathbb{H}$ is the open upper half plane in $\mathbb{C}$. -/
abbrev S (n d : ℕ) : Set (H n d) := { f | IsStable f.1 ∧ ∀ m, 0 ≤ f.1.coeff m }

/-- **The set of Lorentzian polynomials.** For natural numbers $n$ and $d$, the set $L^d_n$ of
Lorentzian polynomials is a set of homogeneous polynomials of degree $d$ in
$\mathbb{R}[w_1, \dots, w_n]$, defined by recursion on $d$. For $d \le 2$, $L^d_n = S^d_n$, the set
of homogeneous stable polynomials of degree $d$ with nonnegative coefficients. For $d \ge 3$,
$L^d_n$ is the set of $f \in M^d_n$ (the homogeneous polynomials of degree $d$ with nonnegative
coefficients and M-convex support) such that $\partial_i f \in L^{d-1}_n$ for every
$i \in \{1, \dots, n\}$, where $\partial_i$ is the partial derivative with respect to $w_i$. -/
def L (n d : ℕ) : Set (H n d) := match d with
  | 0 => S n 0
  | 1 => S n 1
  | 2 => S n 2
  | d + 3 => { f ∈ M n (d + 3) | ∀ i, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (d + 2) }

end LorentzianPolynomials

end MathlibExt.Combinatorics.LorentzianPolynomialsWanted
