/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

/-!
Provenance: concept `jis_sem_f9bc27c2fb50e959e168b460`
(`generalized Fibonacci polynomial sequence`); source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general` from
`jis_source_f9d72107307ec9892cf536d9`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Generalized Fibonacci polynomials.** Given polynomials $p_0, p_1, d, g \in \mathbb{Z}[X]$,
the generalized Fibonacci polynomial sequence $(G_n)_{n \ge 0}$ in $\mathbb{Z}[X]$ is defined by
$G_0 = p_0$, $G_1 = p_1$ and $G_{n+2} = d \, G_{n+1} + g \, G_n$ for every natural number $n$.

Source: concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clauses `coefficient_domain`, `initial_zero`, `initial_one`, `recurrence`). -/
noncomputable def generalizedFibonacciPolynomial
    (p0 p1 d g : Polynomial ℤ) : ℕ → Polynomial ℤ
  | 0 => p0
  | 1 => p1
  | (n + 2) =>
    d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
      g * generalizedFibonacciPolynomial p0 p1 d g n

/-- **Index-zero term of a generalized Fibonacci polynomial sequence.** For all polynomials
$p_0, p_1, d, g \in \mathbb{Z}[X]$, the generalized Fibonacci polynomial sequence $(G_n)$ with
initial terms $p_0, p_1$ and recurrence coefficients $d, g$ has $G_0 = p_0$.

Source: concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clause `initial_zero`). -/
@[simp]
theorem generalizedFibonacciPolynomial_zero
    (p0 p1 d g : Polynomial ℤ) :
    generalizedFibonacciPolynomial p0 p1 d g 0 = p0 := rfl

/-- **Index-one term of a generalized Fibonacci polynomial sequence.** For all polynomials
$p_0, p_1, d, g \in \mathbb{Z}[X]$, the generalized Fibonacci polynomial sequence $(G_n)$ with
initial terms $p_0, p_1$ and recurrence coefficients $d, g$ has $G_1 = p_1$.

Source: concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clause `initial_one`). -/
@[simp]
theorem generalizedFibonacciPolynomial_one
    (p0 p1 d g : Polynomial ℤ) :
    generalizedFibonacciPolynomial p0 p1 d g 1 = p1 := rfl

/-- **Recurrence for generalized Fibonacci polynomials.** For all polynomials $p_0, p_1, d, g$
in $\mathbb{Z}[X]$ and every natural number $n$, the generalized Fibonacci polynomial sequence
$(G_m)$ with initial terms $p_0, p_1$ and recurrence coefficients $d, g$ satisfies
$G_{n+2} = d \, G_{n+1} + g \, G_n$.

Source: concept `jis_sem_f9bc27c2fb50e959e168b460`; source statement
`jis_source_f9d72107307ec9892cf536d9#Fibonacci-general`
(clause `recurrence`). -/
@[simp]
theorem generalizedFibonacciPolynomial_add_two
    (p0 p1 d g : Polynomial ℤ) (n : ℕ) :
    generalizedFibonacciPolynomial p0 p1 d g (n + 2) =
      d * generalizedFibonacciPolynomial p0 p1 d g (n + 1) +
        g * generalizedFibonacciPolynomial p0 p1 d g n := rfl

end

end MetaMathlibExt
