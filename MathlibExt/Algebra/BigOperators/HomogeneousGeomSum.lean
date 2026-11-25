/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Ring

/-!
# Product formula for homogeneous geometric sums
-/

namespace MetaMathlibExt

/-- **Product formula for homogeneous sums of powers.** Let $R$ be a commutative ring, let
$a, b \in R$ and let $\tau, \xi$ be natural numbers. Then
$$
\sum_{j=0}^{\tau+\xi} a^j b^{\tau+\xi-j} =
\left(\sum_{j=0}^{\tau} a^j b^{\tau-j}\right) \left(\sum_{i=0}^{\xi} a^i b^{\xi-i}\right) -
ab \left(\sum_{j=0}^{\tau-1} a^j b^{\tau-1-j}\right)
\left(\sum_{i=0}^{\xi-1} a^i b^{\xi-1-i}\right),
$$
where a sum with upper limit $-1$ is zero.

In the source, $a$ and $b$ are the values $u(n)$ and $v(n)$ of complex arithmetic functions.

Source: André Pierro de Camargo, *Weighted Summation of Dirichlet Convolutions and Applications
to Some Divisor Problems over k-Free and B-Free Integers*, INTEGERS 24 (2024), Article A75,
Lemma 1, Equation (16) (`integers-2024-A75-lem-1`). -/
public theorem sum_pow_mul_pow_add_eq {R : Type*} [CommRing R] (a b : R) (τ ξ : ℕ) :
    ∑ j ∈ Finset.range (τ + ξ + 1), a ^ j * b ^ (τ + ξ - j) =
      (∑ j ∈ Finset.range (τ + 1), a ^ j * b ^ (τ - j)) *
          (∑ i ∈ Finset.range (ξ + 1), a ^ i * b ^ (ξ - i)) -
        a * b * (∑ j ∈ Finset.range τ, a ^ j * b ^ (τ - 1 - j)) *
          (∑ i ∈ Finset.range ξ, a ^ i * b ^ (ξ - 1 - i)) := by
  let S (n : ℕ) := ∑ j ∈ Finset.range n, a ^ j * b ^ (n - 1 - j)
  have step (n : ℕ) : S (n + 1) = a ^ n + b * S n := geom_sum₂_succ_eq a b
  change S (τ + ξ + 1) = S (τ + 1) * S (ξ + 1) - a * b * S τ * S ξ
  induction ξ with
  | zero => simp [S]
  | succ ξ ih =>
    rw [← Nat.add_assoc τ ξ 1, step (τ + ξ + 1), ih, step (ξ + 1), step ξ, step τ]
    simp only [pow_add, pow_one]
    ring

end MetaMathlibExt
