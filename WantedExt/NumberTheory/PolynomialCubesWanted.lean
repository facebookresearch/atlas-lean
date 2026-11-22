/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Expressing an integer as a sum of cubes of polynomials

Statements from Ajai Choudhry, "Expressing an Integer as a Sum of Cubes
of Polynomials", *INTEGERS* 24 (2024), Article A26
(<https://math.colgate.edu/~integers/y26/y26.pdf>).

An integer `N` is represented by the constant polynomial `Polynomial.C N`.
Following the paper's polynomial-identity convention, every witness is
nonconstant: each has `1 ≤ natDegree`. Without that condition, constant
witnesses would reduce the claims to elementary sums of integer cubes.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.PolynomialCubesWanted

/-- **Integers of the form $p^3 + q^3$ or $2(p^6 - q^6)$ as sums of four polynomial cubes.**
Let $p$ and $q$ be integers and let $N = p^3 + q^3$ or $N = 2(p^6 - q^6)$. Then there are
polynomials $f, g, h, k \in \mathbb{Z}[x]$, each of degree at least $1$, such that
$f^3 + g^3 + h^3 + k^3 = N$ as an identity in $\mathbb{Z}[x]$.

Source: Ajai Choudhry, "Expressing an Integer as a Sum of Cubes of
Polynomials", Theorem 1. -/
theorem_wanted int_sum_four_polynomial_cubes_of_cube_form
    (N p q : ℤ)
    (hN : N = p ^ 3 + q ^ 3 ∨ N = 2 * (p ^ 6 - q ^ 6)) :
    ∃ f g h k : Polynomial ℤ,
      1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧
        1 ≤ k.natDegree ∧
        f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 = Polynomial.C N

/-- **Every integer is a sum of five cubes of polynomials.** For every integer $N$ there are
polynomials $f, g, h, k, l \in \mathbb{Z}[x]$, each of degree at least $1$, such that
$f^3 + g^3 + h^3 + k^3 + l^3 = N$ as an identity in $\mathbb{Z}[x]$.

Source: Ajai Choudhry, "Expressing an Integer as a Sum of Cubes of
Polynomials", Theorem 2. -/
theorem_wanted int_eq_sum_five_polynomial_cubes (N : ℤ) :
    ∃ f g h k l : Polynomial ℤ,
      1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧ 1 ≤ h.natDegree ∧
        1 ≤ k.natDegree ∧ 1 ≤ l.natDegree ∧
        f ^ 3 + g ^ 3 + h ^ 3 + k ^ 3 + l ^ 3 = Polynomial.C N

end MathlibExt.NumberTheory.PolynomialCubesWanted
