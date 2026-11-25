/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.ZMod.Basic

/-!
# Integer polynomial maps

An integer polynomial map is represented by a finite family of multivariate polynomials over
`ℤ`. The definitions below provide evaluation over the integers, reduction modulo a natural
number, and iteration in the equal-dimension case.

Source: Alexander Borisov, *Iterations of Integer Polynomial Maps Modulo Primes*,
Journal of Integer Sequences 16 (2013),
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Borisov/borisov3.tex>.

JIS concept: `jis_sem_0d1bf4f3398a408e8cd23d26`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Integer polynomial map.** For natural numbers $n$ and $m$, an integer polynomial map from
$n$ variables to $m$ components is an $m$-tuple $F = (F_0, \dots, F_{m-1})$ of polynomials with
integer coefficients in the $n$ variables $x_0, \dots, x_{n-1}$. -/
def IntegerPolynomialMap (n m : ℕ) : Type :=
  Fin m → MvPolynomial (Fin n) ℤ

/-- **Evaluation of an integer polynomial map.** Let $F = (F_0, \dots, F_{m-1})$ be an integer
polynomial map from $n$ variables to $m$ components. The value of $F$ at a point
$x \in \mathbb{Z}^n$ is the point $(F_0(x), \dots, F_{m-1}(x)) \in \mathbb{Z}^m$. -/
noncomputable def IntegerPolynomialMap.toFun {n m : ℕ}
    (F : IntegerPolynomialMap n m) (x : Fin n → ℤ) : Fin m → ℤ :=
  fun i ↦ MvPolynomial.eval x (F i)

/-- **Reduction of an integer polynomial map modulo a natural number.** Let
$F = (F_0, \dots, F_{m-1})$ be an integer polynomial map from $n$ variables to $m$ components and
let $p$ be a natural number. For $x \in (\mathbb{Z}/p\mathbb{Z})^n$, the value of the reduction of
$F$ modulo $p$ at $x$ is $(\bar F_0(x), \dots, \bar F_{m-1}(x)) \in (\mathbb{Z}/p\mathbb{Z})^m$,
where $\bar F_i$ is the polynomial obtained from $F_i$ by reducing its coefficients modulo $p$.

The definition allows an arbitrary natural modulus; the source applies it when $p$ is prime.
-/
noncomputable def IntegerPolynomialMap.toFunReduce {n m : ℕ}
    (F : IntegerPolynomialMap n m) (p : ℕ) (x : Fin n → ZMod p) : Fin m → ZMod p :=
  fun i ↦ MvPolynomial.eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) (F i))

/-- **Iterates of an integer polynomial map.** Let $F$ be an integer polynomial map from $n$
variables to $n$ components, viewed as the map $\mathbb{Z}^n \to \mathbb{Z}^n$ given by
evaluation. For a natural number $k$ and $x \in \mathbb{Z}^n$, the $k$-th iterate of $F$ at $x$ is
$F^k(x)$, the result of applying $F$ to $x$ exactly $k$ times; in particular $F^0(x) = x$. -/
noncomputable def IntegerPolynomialMap.iterate {n : ℕ}
    (F : IntegerPolynomialMap n n) (k : ℕ) (x : Fin n → ℤ) : Fin n → ℤ :=
  Nat.iterate F.toFun k x

/-- **Iterates of an integer polynomial map modulo a natural number.** Let $F$ be an integer
polynomial map from $n$ variables to $n$ components, let $p$ be a natural number, and let
$\bar F \colon (\mathbb{Z}/p\mathbb{Z})^n \to (\mathbb{Z}/p\mathbb{Z})^n$ be the map obtained by
reducing the coefficients of $F$ modulo $p$ and evaluating. For a natural number $k$ and
$x \in (\mathbb{Z}/p\mathbb{Z})^n$, the $k$-th iterate of $F$ modulo $p$ at $x$ is $\bar F^k(x)$,
the result of applying $\bar F$ to $x$ exactly $k$ times; in particular $\bar F^0(x) = x$. -/
noncomputable def IntegerPolynomialMap.iterateReduce {n : ℕ}
    (F : IntegerPolynomialMap n n) (p k : ℕ) (x : Fin n → ZMod p) : Fin n → ZMod p :=
  Nat.iterate (F.toFunReduce p) k x

end

end MetaMathlibExt
