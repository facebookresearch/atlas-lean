/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.Defs

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-! Generalized Stirling numbers `𝔖_{s;h}(n, k)` from JIS VOL15/Schork,
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Schork/schork2.tex>, lines 154–160,
SHA-256 `f3006b7ef496c012bfca9644eaec996857fb2b465fcb0f7de1a9807e3eb1d659`.

Concept `jis_term_0fc9852339ef66823c96d1ac` (semantic concept
`jis_sem_bc9000de6649aba0f779d229`). The source recurrence is
`𝔖_{s;h}(n+1,k) = 𝔖_{s;h}(n,k-1) + h * (k + s * (n-k)) * 𝔖_{s;h}(n,k)`.

In the Lean pattern `(n + 1, k + 1)`, source `k` is `k + 1`, so the factor is
`h * ((k + 1) + s * (n - (k + 1)))`. Above-diagonal terms remain zero, so
truncated natural-number subtraction does not alter those values. -/
def genStirling {R : Type*} [CommRing R] (s h : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 =>
    genStirling s h n k +
      h * ((↑(k + 1) : R) + s * (↑(n - (k + 1)) : R)) *
        genStirling s h n (k + 1)

/-- **Generalized Bell numbers.** For a commutative ring $R$, elements $s, h \in R$ and a natural
number $n$, the generalized Bell number is
$$\mathfrak{B}_{s;h}(n) = \sum_{k=0}^{n} \mathfrak{S}_{s;h}(n, k),$$
where the generalized Stirling numbers $\mathfrak{S}_{s;h}(a, j) \in R$ are defined for all
natural numbers $a$ and $j$ by $\mathfrak{S}_{s;h}(0, 0) = 1$,
$\mathfrak{S}_{s;h}(0, j + 1) = \mathfrak{S}_{s;h}(a + 1, 0) = 0$ and
$\mathfrak{S}_{s;h}(a + 1, j + 1) = \mathfrak{S}_{s;h}(a, j) +
h\,(j + 1 + s \max(a - j - 1, 0))\,\mathfrak{S}_{s;h}(a, j + 1)$; here the natural number
$\max(a - j - 1, 0)$ is viewed as an element of $R$. -/
def genBellNumber {R : Type*} [CommRing R] (s h : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), genStirling s h n k

/-- **Generalized Bell polynomials.** For a commutative ring $R$, elements $s, h \in R$, a natural
number $n$ and $x \in R$, the generalized Bell polynomial evaluated at $x$ is
$$\mathfrak{B}_{s;h|n}(x) = \sum_{k=0}^{n} \mathfrak{S}_{s;h}(n, k)\, x^k,$$
where the generalized Stirling numbers $\mathfrak{S}_{s;h}(a, j) \in R$ are defined for all
natural numbers $a$ and $j$ by $\mathfrak{S}_{s;h}(0, 0) = 1$,
$\mathfrak{S}_{s;h}(0, j + 1) = \mathfrak{S}_{s;h}(a + 1, 0) = 0$ and
$\mathfrak{S}_{s;h}(a + 1, j + 1) = \mathfrak{S}_{s;h}(a, j) +
h\,(j + 1 + s \max(a - j - 1, 0))\,\mathfrak{S}_{s;h}(a, j + 1)$; here the natural number
$\max(a - j - 1, 0)$ is viewed as an element of $R$. -/
def genBellPolynomial {R : Type*} [CommRing R] (s h : R) (n : ℕ) (x : R) : R :=
  ∑ k ∈ Finset.range (n + 1), genStirling s h n k * x ^ k

@[simp]
theorem genStirling_zero_zero {R : Type*} [CommRing R] (s h : R) :
    genStirling s h 0 0 = 1 := rfl

@[simp]
theorem genStirling_zero_succ {R : Type*} [CommRing R] (s h : R) (k : ℕ) :
    genStirling s h 0 (k + 1) = 0 := rfl

@[simp]
theorem genStirling_succ_zero {R : Type*} [CommRing R] (s h : R) (n : ℕ) :
    genStirling s h (n + 1) 0 = 0 := rfl

/-- **Recurrence for generalized Stirling numbers.** Let $R$ be a commutative ring and
$s, h \in R$. The generalized Stirling numbers $\mathfrak{S}_{s;h}(n, k) \in R$ are defined by
$\mathfrak{S}_{s;h}(0, 0) = 1$, $\mathfrak{S}_{s;h}(0, k + 1) = \mathfrak{S}_{s;h}(n + 1, 0) = 0$
and the recurrence below. For all natural numbers $n$ and $k$,
$$\mathfrak{S}_{s;h}(n + 1, k + 1) = \mathfrak{S}_{s;h}(n, k) +
h\,(k + 1 + s \max(n - k - 1, 0))\,\mathfrak{S}_{s;h}(n, k + 1).$$
Here $\max(n - k - 1, 0)$ is a natural number viewed as an element of $R$. -/
theorem genStirling_succ_succ {R : Type*} [CommRing R] (s h : R) (n k : ℕ) :
    genStirling s h (n + 1) (k + 1) = genStirling s h n k +
      h * ((↑(k + 1) : R) + s * (↑(n - (k + 1)) : R)) *
        genStirling s h n (k + 1) :=
  rfl

/-- **Generalized Bell polynomials at one.** For a commutative ring $R$, elements $s, h \in R$ and
a natural number $n$, the generalized Bell polynomial $\mathfrak{B}_{s;h|n}$ evaluated at $x = 1$
equals the generalized Bell number $\mathfrak{B}_{s;h}(n)$. -/
theorem genBellPolynomial_eval_one {R : Type*} [CommRing R] (s h : R) (n : ℕ) :
    genBellPolynomial s h n 1 = genBellNumber s h n := by
  simp [genBellPolynomial, genBellNumber]

end

end MetaMathlibExt
