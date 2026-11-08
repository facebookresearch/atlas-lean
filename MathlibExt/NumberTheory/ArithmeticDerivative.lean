/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

/-!
# The arithmetic derivative

The arithmetic derivative on `ℕ`, `D(n) = ∑_{p ∣ n} ν_p(n) · (n / p)`, with its basic
characteristic API: `D(0) = D(1) = 0`, `D(p) = 1` for primes `p`, the defining sum over any
superset of the prime factors, and the Leibniz rule `D(mn) = D(m) n + m D(n)`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The arithmetic derivative `D(n) = ∑_{p ∣ n} ν_p(n) · (n / p)` on `ℕ`, with
`D(0) = D(1) = 0`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2,
equation (2). -/
def arithmeticDerivative (n : ℕ) : ℕ :=
  ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

/-- `D(0) = 0`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem arithmeticDerivative_zero : arithmeticDerivative 0 = 0 := by
  simp [arithmeticDerivative]

/-- `D(1) = 0`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem arithmeticDerivative_one : arithmeticDerivative 1 = 0 := by
  simp [arithmeticDerivative]

/-- `D(p) = 1` for every prime `p`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2. -/
theorem arithmeticDerivative_prime {p : ℕ} (hp : p.Prime) : arithmeticDerivative p = 1 := by
  simp [arithmeticDerivative, hp.primeFactors, hp.factorization_self, Nat.div_self hp.pos]

/-- The defining sum may be taken over any finite set containing the prime factors.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2,
equation (2). -/
theorem arithmeticDerivative_eq_sum_of_subset {n : ℕ} {s : Finset ℕ}
    (hs : n.primeFactors ⊆ s) :
    arithmeticDerivative n = ∑ p ∈ s, n.factorization p * (n / p) := by
  refine Finset.sum_subset hs fun p _ hp => ?_
  rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
  simp [hp]

/-- The Leibniz rule `D(mn) = D(m) n + m D(n)`.

Source: Zachary P. Bradshaw, *On a Family of Solutions to Arithmetic Differential Equations
Involving the Collatz Map*, Journal of Integer Sequences 28 (2025), Article 25.1.8, Section 2,
equation (1). -/
theorem arithmeticDerivative_mul (m n : ℕ) :
    arithmeticDerivative (m * n) =
      arithmeticDerivative m * n + m * arithmeticDerivative n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [arithmeticDerivative_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [arithmeticDerivative_zero]
  have hm0 : m ≠ 0 := hm.ne'
  have hn0 : n ≠ 0 := hn.ne'
  set s := (m * n).primeFactors with hsdef
  have hms : m.primeFactors ⊆ s := by
    rw [hsdef, Nat.primeFactors_mul hm0 hn0]; exact Finset.subset_union_left
  have hns : n.primeFactors ⊆ s := by
    rw [hsdef, Nat.primeFactors_mul hm0 hn0]; exact Finset.subset_union_right
  rw [arithmeticDerivative_eq_sum_of_subset hms, arithmeticDerivative_eq_sum_of_subset hns,
    arithmeticDerivative, ← hsdef, Nat.factorization_mul hm0 hn0, Finset.sum_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.add_apply, add_mul]
  congr 1
  · by_cases h : m.factorization p = 0
    · simp [h]
    · rw [mul_assoc, Nat.div_mul_right_comm (Nat.dvd_of_factorization_pos h)]
  · by_cases h : n.factorization p = 0
    · simp [h]
    · rw [Nat.mul_div_assoc m (Nat.dvd_of_factorization_pos h)]
      ring

end

end MetaMathlibExt
