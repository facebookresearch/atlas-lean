/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-!
# Primitive divisors of Lucas-sequence terms

This module isolates the primitive-divisor predicate used for Lucas and related
integer sequences. The discriminant parameter is `(α - β) ^ 2` for a Lucas
pair `(α, β)`.

## References

* Haojie Hong, *On big primitive divisors of Fibonacci numbers*,
  [arXiv:2312.04354v1](https://arxiv.org/abs/2312.04354),
  `bigPFn.tex` lines 153–158 (primitive-divisor definition:
  `p ∣ uₙ` but `p ∤ (α-β)² u₁ ⋯ uₙ₋₁`).
-/

open scoped BigOperators

namespace LucasSequence

/-- **Primitive divisor relative to a discriminant.** Let $u_0, u_1, u_2, \dots$ be a sequence
of integers and let $D$ be an integer (for a Lucas pair $(\alpha, \beta)$, the discriminant
$D = (\alpha - \beta)^2$). A natural number $p$ is a primitive divisor of $u_n$ when $n \ge 1$, $p$
is prime, $p$ divides $u_n$, and $p$ does not divide $D \, u_1 u_2 \cdots u_{n-1}$ (for $n = 1$ the
product is empty, and the condition is that $p$ does not divide $D$). -/
def IsPrimitiveDivisor (u : ℕ → ℤ) (discriminant : ℤ) (n p : ℕ) : Prop :=
  0 < n ∧ p.Prime ∧ (p : ℤ) ∣ u n ∧
    ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k

theorem IsPrimitiveDivisor.pos {u : ℕ → ℤ} {discriminant : ℤ} {n p : ℕ}
    (h : IsPrimitiveDivisor u discriminant n p) : 0 < n :=
  h.1

theorem IsPrimitiveDivisor.prime {u : ℕ → ℤ} {discriminant : ℤ} {n p : ℕ}
    (h : IsPrimitiveDivisor u discriminant n p) : p.Prime :=
  h.2.1

theorem IsPrimitiveDivisor.dvd_term {u : ℕ → ℤ} {discriminant : ℤ} {n p : ℕ}
    (h : IsPrimitiveDivisor u discriminant n p) : (p : ℤ) ∣ u n :=
  h.2.2.1

theorem IsPrimitiveDivisor.not_dvd_badPart {u : ℕ → ℤ}
    {discriminant : ℤ} {n p : ℕ} (h : IsPrimitiveDivisor u discriminant n p) :
    ¬(p : ℤ) ∣ discriminant * ∏ k ∈ Finset.Ico 1 n, u k :=
  h.2.2.2

theorem IsPrimitiveDivisor.not_dvd_discriminant {u : ℕ → ℤ}
    {discriminant : ℤ} {n p : ℕ} (h : IsPrimitiveDivisor u discriminant n p) :
    ¬(p : ℤ) ∣ discriminant := by
  intro hp
  exact h.not_dvd_badPart (dvd_mul_of_dvd_left hp _)

theorem IsPrimitiveDivisor.not_dvd_prior {u : ℕ → ℤ} {discriminant : ℤ}
    {n p k : ℕ} (h : IsPrimitiveDivisor u discriminant n p)
    (hk : k ∈ Finset.Ico 1 n) : ¬(p : ℤ) ∣ u k := by
  intro hp
  apply h.not_dvd_badPart
  exact dvd_mul_of_dvd_right (dvd_trans hp (Finset.dvd_prod_of_mem u hk)) _

end LucasSequence
