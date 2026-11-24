/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPrime
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Fifth-power bound on the Euler prime

In the Eulerian form `n = q ^ e * m ^ 2` of an odd perfect number, either the exponent is one
or the fifth power of the Euler prime is less than twice the square part.
-/

namespace MetaMathlibExt

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **Fifth-power bound on the Euler prime of an odd perfect number.** If $(n, q, e, m)$ is in
Eulerian form, that is, $n$ is an odd perfect number, $q$ is a prime coprime to $m$,
$n = q^e m^2$ and $q \equiv e \equiv 1 \pmod 4$, then $e = 1$ or $q^5 < 2m^2$, that is,
$q < 2^{1/5} m^{2/5}$.

Source: Joshua Zelinsky, *The Sum of the Reciprocals of the Prime Divisors of an Odd
Perfect or Odd Primitive Non-deficient Number*, INTEGERS 25 (2025), Article A59,
Proposition 11 (`integers-2025-A59-prop-11`). -/
public theorem eulerianForm_exponent_eq_one_or_pow_five_lt
    (n q e m : ℕ) (h : EulerianForm n q e m) :
    e = 1 ∨ q ^ 5 < 2 * m ^ 2 := by
  obtain ⟨hperf, _, hq, rfl, _, he, hcop⟩ := h
  by_cases h₁ : e = 1
  · exact Or.inl h₁
  right
  have h₅ : 5 ≤ e := by omega
  have hm : 0 < m ^ 2 := Nat.pos_of_mul_pos_left hperf.2
  -- The geometric sum is one modulo q, so it is coprime to the Euler prime power.
  have hcopSum : q.Coprime (σ 1 (q ^ e)) := by
    simp [sigma_one_apply_prime_pow hq, geom_sum_succ]
  have hprod := (Nat.perfect_iff_sum_divisors_eq_two_mul hperf.2).mp hperf
  rw [← sigma_one_apply, isMultiplicative_sigma.map_mul_of_coprime
    ((hcop.pow_left e).pow_right 2), mul_left_comm 2] at hprod
  have hdvd : σ 1 (q ^ e) ∣ 2 * m ^ 2 :=
    (hcopSum.symm.pow_right e).dvd_of_dvd_mul_left (hprod ▸ dvd_mul_right _ _)
  calc
    q ^ 5 ≤ q ^ e := Nat.pow_le_pow_right hq.pos h₅
    _ < σ 1 (q ^ e) := by
      rw [sigma_one_apply_prime_pow hq, geom_sum_succ']
      exact Nat.lt_add_of_pos_right (geom_sum_pos q.zero_le (by omega))
    _ ≤ 2 * m ^ 2 := Nat.le_of_dvd (by omega) hdvd

end MetaMathlibExt
