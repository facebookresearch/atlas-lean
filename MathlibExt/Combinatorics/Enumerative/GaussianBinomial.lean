/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Gaussian binomial coefficients and finite q-Pochhammer symbols

Shared finite q-series layer: the Gaussian binomial coefficient `gaussBinom`,
defined by the Pascal recursion in `M`, the finite q-Pochhammer symbol
`qPochFin`, and the product formula relating them.
-/

namespace MathlibExt

/-- **Gaussian binomial coefficient.** Let $R$ be a semiring and $Q \in R$. For natural numbers
$M$ and $k$, the Gaussian binomial coefficient $\binom{M}{k}_Q \in R$ is defined recursively by
$\binom{M}{0}_Q = 1$, $\binom{0}{k+1}_Q = 0$ and
$\binom{M+1}{k+1}_Q = \binom{M}{k}_Q + Q^{k+1} \binom{M}{k+1}_Q$. -/
def gaussBinom {R : Type*} [Semiring R] (Q : R) (M : ℕ) : ℕ → R
  | 0 => 1
  | k + 1 =>
      match M with
      | 0 => 0
      | M + 1 => gaussBinom Q M k + Q ^ (k + 1) * gaussBinom Q M (k + 1)

/-- **Gaussian binomial coefficients with $k = 0$.** Let $R$ be a semiring and $Q \in R$. For
every natural number $M$, the Gaussian binomial coefficient $\binom{M}{0}_Q$ equals $1$. -/
@[simp]
theorem gaussBinom_zero_right {R : Type*} [Semiring R] (Q : R) (M : ℕ) :
    gaussBinom Q M 0 = 1 := by
  simp [gaussBinom]

/-- **Gaussian binomial coefficients with $M = 0$.** Let $R$ be a semiring and $Q \in R$. For
every natural number $k$, the Gaussian binomial coefficient $\binom{0}{k+1}_Q$ equals $0$. -/
@[simp]
theorem gaussBinom_zero_succ {R : Type*} [Semiring R] (Q : R) (k : ℕ) :
    gaussBinom Q 0 (k + 1) = 0 := by
  simp [gaussBinom]

/-- **$Q$-Pascal recursion for Gaussian binomial coefficients.** Let $R$ be a semiring and
$Q \in R$. For all natural numbers $M$ and $k$, the Gaussian binomial coefficients satisfy
$\binom{M+1}{k+1}_Q = \binom{M}{k}_Q + Q^{k+1} \binom{M}{k+1}_Q$. -/
theorem gaussBinom_succ_succ {R : Type*} [Semiring R] (Q : R)
    (M k : ℕ) :
    gaussBinom Q (M + 1) (k + 1)
      = gaussBinom Q M k + Q ^ (k + 1) * gaussBinom Q M (k + 1) := by
  simp [gaussBinom]

/-- **Gaussian binomial coefficients vanish when $k > M$.** Let $R$ be a semiring and $Q \in R$.
For natural numbers $M$ and $k$ with $M < k$, the Gaussian binomial coefficient $\binom{M}{k}_Q$
is $0$. -/
theorem gaussBinom_eq_zero_of_lt {R : Type*} [Semiring R] (Q : R)
    (M k : ℕ) (h : M < k) : gaussBinom Q M k = 0 := by
  induction M generalizing k with
  | zero =>
      cases k with
      | zero => omega
      | succ k => exact gaussBinom_zero_succ Q k
  | succ M ih =>
      cases k with
      | zero => omega
      | succ k =>
          rw [gaussBinom_succ_succ, ih k (by omega), ih (k + 1) (by omega)]
          simp

/-- **Diagonal Gaussian binomial coefficients.** Let $R$ be a semiring and $Q \in R$. For every
natural number $M$, the Gaussian binomial coefficient $\binom{M}{M}_Q$ equals $1$. -/
@[simp]
theorem gaussBinom_self {R : Type*} [Semiring R] (Q : R) (M : ℕ) :
    gaussBinom Q M M = 1 := by
  induction M with
  | zero => exact gaussBinom_zero_right Q 0
  | succ M ih =>
      rw [gaussBinom_succ_succ, ih,
        gaussBinom_eq_zero_of_lt Q M (M + 1) (Nat.lt_succ_self M)]
      simp

/-- **Finite $Q$-Pochhammer symbol.** Let $R$ be a commutative ring and $Q \in R$. For a natural
number $m$, the finite $Q$-Pochhammer symbol $P_Q(m) \in R$ is the product
$\prod_{i < m} (1 - Q^{i+1})$ of $1 - Q^{i+1}$ over the natural numbers $i < m$. -/
def qPochFin {R : Type*} [CommRing R] (Q : R) (m : ℕ) : R :=
  ∏ i ∈ Finset.range m, (1 - Q ^ (i + 1))

/-- **The finite $Q$-Pochhammer symbol at $0$.** Let $R$ be a commutative ring and $Q \in R$. The
finite $Q$-Pochhammer symbol $P_Q(m) = \prod_{i < m} (1 - Q^{i+1})$, the product running over the
natural numbers $i < m$, satisfies $P_Q(0) = 1$. -/
@[simp]
theorem qPochFin_zero {R : Type*} [CommRing R] (Q : R) :
    qPochFin Q 0 = 1 := by
  simp [qPochFin]

/-- **Recursion for the finite $Q$-Pochhammer symbol.** Let $R$ be a commutative ring and
$Q \in R$, and write $P_Q(m) = \prod_{i < m} (1 - Q^{i+1})$ for the finite $Q$-Pochhammer symbol,
the product running over the natural numbers $i < m$. For every natural number $m$,
$P_Q(m+1) = P_Q(m) \, (1 - Q^{m+1})$. -/
theorem qPochFin_succ {R : Type*} [CommRing R] (Q : R) (m : ℕ) :
    qPochFin Q (m + 1) = qPochFin Q m * (1 - Q ^ (m + 1)) := by
  simp [qPochFin, Finset.prod_range_succ]

/-- **Product formula for Gaussian binomial coefficients.** Let $R$ be a commutative ring and
$Q \in R$, and write $P_Q(m) = \prod_{i < m} (1 - Q^{i+1})$ for the finite $Q$-Pochhammer symbol,
the product running over the natural numbers $i < m$. For natural numbers $k \le M$, the Gaussian
binomial coefficient satisfies $\binom{M}{k}_Q \, P_Q(k) \, P_Q(M - k) = P_Q(M)$. -/
theorem gaussBinom_mul_qPochFin_mul_qPochFin {R : Type*}
    [CommRing R] (Q : R) (M k : ℕ) (h : k ≤ M) :
    gaussBinom Q M k * qPochFin Q k * qPochFin Q (M - k)
      = qPochFin Q M := by
  induction M generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst hk
      simp
  | succ M ih =>
      cases k with
      | zero =>
          simp
      | succ k =>
          by_cases hjk : k = M
          · rw [hjk]
            rw [gaussBinom_self]
            have hsub0 : M + 1 - (M + 1) = 0 := by omega
            rw [hsub0]
            simp
          · have h1 : k ≤ M := by omega
            have h2 : k + 1 ≤ M := by omega
            have hsub : M + 1 - (k + 1) = M - k := by omega
            rw [hsub, gaussBinom_succ_succ]
            have hPk : qPochFin Q (k + 1)
                = qPochFin Q k * (1 - Q ^ (k + 1)) :=
              qPochFin_succ Q k
            have hMj : M - k = (M - (k + 1)) + 1 := by omega
            have hMj' : (M - (k + 1)) + 1 = M - k := by omega
            have hPm : qPochFin Q (M - k)
                = qPochFin Q (M - (k + 1)) * (1 - Q ^ (M - k)) := by
              conv_lhs => rw [hMj]
              rw [qPochFin_succ, hMj']
            have hQ : Q ^ (M + 1) = Q ^ (k + 1) * Q ^ (M - k) := by
              rw [← pow_add]
              congr 1
              omega
            have ih1 := ih k h1
            have ih2 := ih (k + 1) h2
            have e1 : gaussBinom Q M k * qPochFin Q (k + 1)
                * qPochFin Q (M - k)
                = (1 - Q ^ (k + 1)) * qPochFin Q M := by
              rw [hPk]
              have hexp : gaussBinom Q M k
                    * (qPochFin Q k * (1 - Q ^ (k + 1)))
                    * qPochFin Q (M - k)
                  = (1 - Q ^ (k + 1))
                    * (gaussBinom Q M k * qPochFin Q k
                      * qPochFin Q (M - k)) := by
                ring
              rw [hexp, ih1]
            have e2 : gaussBinom Q M (k + 1) * qPochFin Q (k + 1)
                * qPochFin Q (M - k)
                = (1 - Q ^ (M - k)) * qPochFin Q M := by
              rw [hPm]
              have hexp : gaussBinom Q M (k + 1) * qPochFin Q (k + 1)
                    * (qPochFin Q (M - (k + 1)) * (1 - Q ^ (M - k)))
                  = (1 - Q ^ (M - k))
                    * (gaussBinom Q M (k + 1) * qPochFin Q (k + 1)
                      * qPochFin Q (M - (k + 1))) := by
                ring
              rw [hexp, ih2]
            have hPM : qPochFin Q (M + 1)
                = qPochFin Q M * (1 - Q ^ (M + 1)) :=
              qPochFin_succ Q M
            have hexpand : (gaussBinom Q M k + Q ^ (k + 1)
                  * gaussBinom Q M (k + 1)) * qPochFin Q (k + 1)
                  * qPochFin Q (M - k)
                = gaussBinom Q M k * qPochFin Q (k + 1)
                    * qPochFin Q (M - k)
                  + Q ^ (k + 1) * (gaussBinom Q M (k + 1)
                    * qPochFin Q (k + 1) * qPochFin Q (M - k)) := by
              ring
            rw [hexpand, e1, e2, hPM, hQ]
            ring

end MathlibExt

end
