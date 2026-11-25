/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import MathlibExt.NumberTheory.QuadraticForms.Reduced
public import MathlibExt.NumberTheory.QuadraticForms.ThreeSquares

/-!
# Gauss class numbers of negative discriminants

This module defines the finite set `reducedFormsOfDiscriminant d` of Gauss-reduced integral
binary quadratic forms of discriminant `d`, computed by a finite search, and the Gauss class
number `gaussClassNumber d`, the number of primitive forms among them. Both follow Aygin and
Williams, *A Note on the Evaluation of Two Arithmetic Functions of Kronecker*, INTEGERS 26
(2026), Article A29, Section 1.
-/

namespace MetaMathlibExt

@[expose] public section

/-- Gauss reducedness of `a * x ^ 2 + b * x * y + c * y ^ 2` is decidable: it is a
conjunction of integer comparisons.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1
(reduced forms `-a < b ≤ a < c` or `0 ≤ b ≤ a = c`, which is
`BinaryQuadraticForm.IsGaussReduced` together with positive definiteness). The instance is
local to this file, so importing it does not change instance search elsewhere. -/
public local instance decidableIsGaussReduced (a b c : ℤ) :
    Decidable (BinaryQuadraticForm.IsGaussReduced a b c) :=
  inferInstanceAs (Decidable (0 < a ∧ discrim a b c < 0 ∧ |b| ≤ a ∧ a ≤ c ∧
    ((|b| = a ∨ a = c) → 0 ≤ b)))

/-- **Reduced forms of a given discriminant.** For an integer $d$, $R(d)$ is the finite set of
integer triples $(a, b, c)$ such that the binary quadratic form $a x^2 + b x y + c y^2$ is Gauss
reduced (that is, $a > 0$, $b^2 - 4ac < 0$, $|b| \le a \le c$, and $b \ge 0$ whenever $|b| = a$ or
$a = c$) and has discriminant $b^2 - 4ac = d$. In particular $R(d)$ is empty when $d \ge 0$.

The set is computed by a finite search: a reduced form satisfies $-d = 4ac - b^2 \ge 3a^2$, so
$1 \le a \le \lfloor \sqrt{-d} \rfloor$ and $|b| \le a$, and $c = (b^2 - d) / (4a)$ is determined
by $a$ and $b$.

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public def reducedFormsOfDiscriminant (d : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (1 : ℤ) (Nat.sqrt (-d).toNat)).biUnion fun a =>
      (Finset.Icc (-a) a).image fun b => (a, b, (b ^ 2 - d) / (4 * a))).filter fun q =>
    BinaryQuadraticForm.IsGaussReduced q.1 q.2.1 q.2.2 ∧ discrim q.1 q.2.1 q.2.2 = d

/-- **Gauss class number of a discriminant.** For an integer $d$, the Gauss class number $h(d)$
is the number of integer triples $(a, b, c)$ with $b^2 - 4ac = d$ for which the binary quadratic
form $ax^2 + bxy + cy^2$ is positive definite ($a > 0$ and $d < 0$), reduced ($|b| \le a \le c$,
with $b \ge 0$ whenever $|b| = a$ or $a = c$) and primitive ($\gcd(a, b, c) = 1$).

Source: Zafer Selcuk Aygin and Kenneth S. Williams, *A Note on the Evaluation of Two
Arithmetic Functions of Kronecker*, INTEGERS 26 (2026), Article A29, Section 1. -/
public def gaussClassNumber (d : ℤ) : ℕ :=
  ((reducedFormsOfDiscriminant d).filter fun q =>
    Int.gcd (Int.gcd q.1 q.2.1 : ℤ) q.2.2 = 1).card

end

end MetaMathlibExt
