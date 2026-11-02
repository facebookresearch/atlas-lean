/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Multigraded polynomial modules

This file provides the `ℤⁿ`-graded module interface over a multivariate
polynomial ring `MvPolynomial (Fin n) K` with the standard monomial
degree-shift action. It is the first named dependency towards the
Braun–Davis multigraded Poincaré-series development.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 856–877. Those lines define multigraded free resolutions and
Betti numbers and state that the multigraded Poincaré series of a finitely
generated graded module over a polynomial ring is a polynomial.

Deliberately deferred (not claimed here): multigraded free resolutions,
independence of the Betti numbers, finite support of the Betti table, and
the final polynomiality theorem for the multigraded Poincaré series.
This file only provides the underlying `ℤⁿ`-graded module object with the
monomial degree-shift law on which those later stages will build.

Main definitions:

* `MetaMathlibExt.natDegreeToInt`: embed a monomial exponent `Fin n →₀ ℕ`
  into the `ℤⁿ` grading index.
* `MetaMathlibExt.MultigradedPolynomialModule`: a `K`-submodule
  decomposition of `M` indexed by `Fin n →₀ ℤ`, compatible with scalars via
  `MvPolynomial.C` and shifting under monomial multiplication by the
  embedded exponent degree.
-/

@[expose] public section

namespace MetaMathlibExt

open MvPolynomial

variable (K : Type*) [Field K] (n : ℕ)

/-- **Exponent vectors as integer vectors.** For an exponent vector
$a = (a_1, \dots, a_n) \in \mathbb{N}^n$ of a monomial, this is the vector
$(a_1, \dots, a_n) \in \mathbb{Z}^n$ obtained by viewing each entry $a_i$ as an integer. -/
public noncomputable def natDegreeToInt {n : ℕ} (a : Fin n →₀ ℕ) : Fin n →₀ ℤ :=
  Finsupp.mapRange (fun x : ℕ => (x : ℤ)) (by simp) a

/-- **Multigraded modules over a polynomial ring.** Let $K$ be a field, $n \in \mathbb{N}$
and $R = K[x_1, \dots, x_n]$, and let $M$ be an $R$-module that is also a $K$-vector
space. A $\mathbb{Z}^n$-grading of $M$ compatible with monomial multiplication consists of
$K$-subspaces $M_\alpha \subseteq M$, one for each $\alpha \in \mathbb{Z}^n$, such that $M$
is the direct sum of the $M_\alpha$, the action of each $k \in K$ on $M$ agrees with
multiplication by the constant polynomial $k \in R$, and for every $a \in \mathbb{N}^n$,
every $c \in K$ and every $\alpha \in \mathbb{Z}^n$, multiplication by the monomial
$c x^a = c x_1^{a_1} \cdots x_n^{a_n}$ maps $M_\alpha$ into $M_{\alpha + a}$, where $a$ is
viewed as an element of $\mathbb{Z}^n$. -/
public structure MultigradedPolynomialModule (M : Type*) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M] where
  /-- The homogeneous `K`-submodule in degree `α`. -/
  component : (Fin n →₀ ℤ) → Submodule K M
  /-- The homogeneous pieces decompose `M` as a direct sum. -/
  decomposition : DirectSum.Decomposition component
  /-- Scalar multiplication by `k : K` agrees with the `MvPolynomial.C k` action. -/
  smul_via_C : ∀ (k : K) (m : M), k • m = ((MvPolynomial.C k : MvPolynomial (Fin n) K)) • m
  /-- Monomials shift homogeneous degrees by the embedded exponent. -/
  monomial_mem : ∀ (a : Fin n →₀ ℕ) (c : K) (α : Fin n →₀ ℤ) (m : M),
    m ∈ component α →
      ((MvPolynomial.monomial a c : MvPolynomial (Fin n) K)) • m ∈
        component (α + natDegreeToInt a)

end MetaMathlibExt
