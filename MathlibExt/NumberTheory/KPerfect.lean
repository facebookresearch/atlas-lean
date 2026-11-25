/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc

@[expose] public section

/-!
# Parameterized perfect numbers

A positive natural number `n` is `k`-perfect when its sum of positive divisors is `k * n`.

## References

* Yoshinosuke Hirakawa, *A note on the Diophantine equation
  2ℓn² = 1 + q + ⋯ + q^α and application to odd perfect numbers*, arXiv:2309.17084v3
-/

namespace Nat

/-- **$k$-perfect numbers.** For natural numbers $k$ and $n$, the number $n$ is $k$-perfect when
$n > 0$ and $\sigma(n) = kn$, where $\sigma(n)$ is the sum of the positive divisors of $n$. -/
def IsKPerfect (k n : ℕ) : Prop :=
  0 < n ∧ (ArithmeticFunction.sigma 1) n = k * n

instance decidableIsKPerfect (k n : ℕ) : Decidable (IsKPerfect k n) := by
  unfold IsKPerfect
  infer_instance

/-- **The parameter of a $k$-perfect number is positive.** For natural numbers $k$ and $n$, if $n$
is $k$-perfect, then $k > 0$. -/
theorem IsKPerfect.pos_k {k n : ℕ} (h : IsKPerfect k n) : 0 < k := by
  have hsigma : 0 < (ArithmeticFunction.sigma 1) n :=
    ArithmeticFunction.sigma_pos 1 n h.1.ne'
  rw [h.2] at hsigma
  exact Nat.pos_of_mul_pos_right hsigma

/-- **Perfect numbers are the $2$-perfect numbers.** A natural number $n$ is $2$-perfect if and
only if it is perfect, that is, $n > 0$ and the sum of the proper divisors of $n$ equals $n$. -/
theorem isKPerfect_two_iff (n : ℕ) : IsKPerfect 2 n ↔ n.Perfect := by
  constructor
  · rintro ⟨hn, hsigma⟩
    rw [ArithmeticFunction.sigma_one_apply] at hsigma
    exact (perfect_iff_sum_divisors_eq_two_mul hn).2 hsigma
  · intro hn
    refine ⟨hn.2, ?_⟩
    rw [ArithmeticFunction.sigma_one_apply]
    exact (perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn

end Nat
