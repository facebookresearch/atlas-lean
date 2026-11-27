/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.Coeff

open scoped BigOperators

namespace MetaMathlibExt

@[expose] public section

/-- **Generating polynomial of the first-kind Jacobi–Stirling numbers.** For a commutative ring
$R$, an element $\zeta \in R$ and a natural number $n$, the $n$-th first-kind Jacobi–Stirling
generating polynomial is $\prod_{i=0}^{n-1} (X - i(i + \zeta))$ in $R[X]$.

Source: concept `jis_sem_108a092cfddb7cc6b11d221e`, source equation `e:JacobiStirling1`. -/
public noncomputable def jacobiStirlingFirstPoly {R : Type*} [CommRing R]
    (n : ℕ) (ζ : R) : Polynomial R :=
  ∏ i ∈ Finset.range n,
    (Polynomial.X - Polynomial.C ((i : R) * ((i : R) + ζ)))

/-- **First-kind Jacobi–Stirling numbers.** For a commutative ring $R$, an element $\zeta \in R$
and natural numbers $n$ and $k$, the first-kind Jacobi–Stirling number $J(n,k;\zeta)$ is the
coefficient of $X^k$ in the polynomial $\prod_{i=0}^{n-1} (X - i(i + \zeta))$ over $R$.

Source: concept `jis_sem_108a092cfddb7cc6b11d221e`, source equation `e:JacobiStirling1`. -/
public noncomputable def jacobiStirlingFirst {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) : R :=
  (jacobiStirlingFirstPoly n ζ).coeff k

/-- **Initial row of the first-kind Jacobi–Stirling numbers.** For every commutative ring $R$,
every $\zeta \in R$ and every natural number $k$, the first-kind Jacobi–Stirling number
$J(0,k;\zeta)$ equals $1$ if $k = 0$ and $0$ otherwise.

Source: concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1` note
`J(0,k;ζ) = δ_{0,k}`. -/
public theorem jacobiStirlingFirst_initial_row {R : Type*} [CommRing R]
    (k : ℕ) (ζ : R) :
    jacobiStirlingFirst 0 k ζ = if k = 0 then 1 else 0 := by
  unfold jacobiStirlingFirst jacobiStirlingFirstPoly
  simp [Polynomial.coeff_one]

/-- **Recurrence for the first-kind Jacobi–Stirling numbers.** For every commutative ring $R$,
every $\zeta \in R$ and all natural numbers $n$ and $k$, the first-kind Jacobi–Stirling numbers
satisfy $J(n+1,k+1;\zeta) = J(n,k;\zeta) - n(n + \zeta)\,J(n,k+1;\zeta)$.

Source: concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1` with factor
`X - n * (n + ζ)`. -/
public theorem jacobiStirlingFirst_recurrence {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) :
    jacobiStirlingFirst (n + 1) (k + 1) ζ =
      jacobiStirlingFirst n k ζ -
        (n : R) * ((n : R) + ζ) * jacobiStirlingFirst n (k + 1) ζ := by
  unfold jacobiStirlingFirst
  have hprod : jacobiStirlingFirstPoly (n + 1) ζ =
      jacobiStirlingFirstPoly n ζ *
        (Polynomial.X - Polynomial.C ((n : R) * ((n : R) + ζ))) := by
    unfold jacobiStirlingFirstPoly
    rw [Finset.prod_range_succ]
  rw [hprod, mul_sub, Polynomial.coeff_sub, Polynomial.coeff_mul_X,
    Polynomial.coeff_mul_C,
    mul_comm ((jacobiStirlingFirstPoly n ζ).coeff (k + 1)) _]

/-- **First-kind Jacobi–Stirling numbers vanish above the diagonal.** For every commutative ring
$R$, every $\zeta \in R$ and all natural numbers $n < k$, the first-kind Jacobi–Stirling number
$J(n,k;\zeta)$ equals $0$.

Source: concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1`. -/
public theorem jacobiStirlingFirst_support {R : Type*} [CommRing R]
    (n k : ℕ) (ζ : R) (h : n < k) :
    jacobiStirlingFirst n k ζ = 0 := by
  induction n generalizing k with
  | zero =>
    have hk : k ≠ 0 := by omega
    have h0 := jacobiStirlingFirst_initial_row k ζ
    rw [ite_eq_right hk] at h0
    exact h0
  | succ n ih =>
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    have h1 : n < m := by omega
    have h2 : n < m + 1 := by omega
    have e1 : jacobiStirlingFirst n m ζ = 0 := ih m h1
    have e2 : jacobiStirlingFirst n (m + 1) ζ = 0 := ih (m + 1) h2
    rw [jacobiStirlingFirst_recurrence, e1, e2, mul_zero, sub_self]

/-- **Diagonal of the first-kind Jacobi–Stirling numbers.** For every commutative ring $R$, every
$\zeta \in R$ and every natural number $n$, the first-kind Jacobi–Stirling number
$J(n,n;\zeta)$ equals $1$.

Source: concept `jis_sem_108a092cfddb7cc6b11d221e`, from `e:JacobiStirling1`. -/
public theorem jacobiStirlingFirst_diagonal {R : Type*} [CommRing R]
    (n : ℕ) (ζ : R) :
    jacobiStirlingFirst n n ζ = 1 := by
  induction n with
  | zero =>
    have h0 := jacobiStirlingFirst_initial_row 0 ζ
    rw [ite_eq_left rfl] at h0
    exact h0
  | succ n ih =>
    rw [jacobiStirlingFirst_recurrence, ih,
      jacobiStirlingFirst_support n (n + 1) ζ (by omega), mul_zero, sub_zero]

end

end MetaMathlibExt
