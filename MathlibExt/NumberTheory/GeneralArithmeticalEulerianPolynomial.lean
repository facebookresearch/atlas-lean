/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# General arithmetical Eulerian polynomials

This file defines the general arithmetical Eulerian numbers and polynomials from Paul Barry,
*General Eulerian Polynomials as Moments Using Exponential Riordan Arrays*:
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Barry4/barry271.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- **General arithmetical Eulerian number.** Let $R$ be a ring, let $n$ and $k$ be natural
numbers, and let $a, d \in R$. The general arithmetical Eulerian number $A_{n,k}(a,d) \in R$ is

$$A_{n,k}(a,d) = \sum_{i=0}^{k} (-1)^i \binom{n+1}{i} \bigl((k+1-i)\,d - a\bigr)^n.$$
-/
def generalArithmeticalEulerianNumber (R : Type*) [Ring R] (n k : ℕ) (a d : R) : R :=
  ∑ i ∈ Finset.range (k + 1),
    (-1 : R) ^ i * (Nat.choose (n + 1) i : R) * ((k + 1 - i : ℕ) * d - a) ^ n

/-- **General arithmetical Eulerian polynomial.** Let $R$ be a ring, let $n$ be a natural number,
and let $a, d \in R$. For each natural number $k$, write $A_{n,k}(a,d) \in R$ for the general
arithmetical Eulerian number. The general arithmetical Eulerian polynomial is the polynomial
in the indeterminate $t$

$$P_n(t;a,d) = \sum_{k=0}^{n} A_{n,k}(a,d)\, t^k \in R[t].$$
-/
noncomputable def generalArithmeticalEulerianPolynomial
    (R : Type*) [Ring R] (n : ℕ) (a d : R) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C (generalArithmeticalEulerianNumber R n k a d) * Polynomial.X ^ k

end MetaMathlibExt
