/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Defs

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

variable {R : Type*} [Semiring R]

/-!
Provenance for the `(q, r)`-Dowling polynomial and number:

- lexical concept `jis_term_a2bc80130d1209c8dec31ca0`;
- semantic concept `jis_sem_21a4a5cbb99f9b622432388e`;
- source statements `jis_936d415cbd90fe97c847cf81` and `jis_8910e171ff1cd000908e919c`;
- JIS VOL18/Mangontarum,
  <https://cs.uwaterloo.ca/journals/JIS/VOL18/Mangontarum/mango2.tex>, SHA-256
  `7eeb8709f4c547fa50ca7b8eb6a005b9b58e0a3e0ff3befac5c3db7c5b23bda1`;
- JIS VOL20/Mangontarum,
  <https://cs.uwaterloo.ca/journals/JIS/VOL20/Mangontarum/mango4.tex>, SHA-256
  `3e6c2cf946c933cf36388d5da99293ed8f39d50de0024290beb39f94ccaa5c5d`.
-/

/-- **$(q, r)$-Dowling polynomial.** Let $R$ be a semiring and let $W(n, k) \in R$ for all
natural numbers $n$ and $k$ (intended to be the $(q, r)$-Whitney numbers of the second kind, but
any family is allowed). For a natural number $n$, the $(q, r)$-Dowling polynomial of $W$ at $n$ is
the polynomial $\sum_{k=0}^{n} W(n, k)\, x^k$ in $R[x]$. -/
noncomputable def qrDowlingPolynomial (W : ℕ → ℕ → R) (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.C (W n k) * Polynomial.X ^ k

/-- **$(q, r)$-Dowling number.** Let $R$ be a semiring and let $W(n, k) \in R$ for all natural
numbers $n$ and $k$. For a natural number $n$, the $(q, r)$-Dowling number of $W$ at $n$ is the
value at $x = 1$ of the $(q, r)$-Dowling polynomial $\sum_{k=0}^{n} W(n, k)\, x^k$ of $W$. -/
noncomputable def qrDowlingNumber (W : ℕ → ℕ → R) (n : ℕ) : R :=
  Polynomial.eval 1 (qrDowlingPolynomial W n)

/-- **$(q, r)$-Dowling numbers as sums of coefficients.** Let $R$ be a semiring and let
$W(n, k) \in R$ for all natural numbers $n$ and $k$. For every natural number $n$, the
$(q, r)$-Dowling number of $W$ at $n$ equals $\sum_{k=0}^{n} W(n, k)$. -/
theorem qrDowlingNumber_eq_sum (W : ℕ → ℕ → R) (n : ℕ) :
    qrDowlingNumber W n = ∑ k ∈ Finset.range (n + 1), W n k := by
  rw [qrDowlingNumber, qrDowlingPolynomial, Polynomial.eval_finsetSum]
  simp

end

end MetaMathlibExt
