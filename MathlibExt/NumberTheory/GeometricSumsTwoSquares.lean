/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares

/-!
# Geometric sums as sums of two squares

Let `p` be prime and `n` positive. If a prime `q` divides the geometric sum with
base `p ^ n` and length `p`, then
`p ^ n` has order `p` modulo `q`. Hence `q ≡ 1 [MOD p]`. When `p ≡ 3 [MOD 4]`
and `n` is odd, `p` is also a square modulo `q`, so quadratic reciprocity rules out
`q ≡ 3 [MOD 4]`.
-/

namespace MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

private theorem prime_divisor_mod_four_ne_three {p n q : ℕ} (hp : p.Prime) (hp4 : p % 4 = 3)
    (hn : Odd n) (hn0 : 0 < n) (hq : q.Prime) (hd : q ∣ ∑ j ∈ Finset.range p, p ^ (n * j)) :
    q % 4 ≠ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hsum : ∑ j ∈ Finset.range p, ((p : ZMod q) ^ n) ^ j = 0 := by
    simpa only [Nat.cast_sum, Nat.cast_pow, pow_mul] using (ZMod.natCast_eq_zero_iff _ q).2 hd
  have hroot : ((p : ZMod q) ^ n) ^ p = 1 := by
    apply sub_eq_zero.mp
    rw [← geom_sum_mul, hsum, zero_mul]
  have hp0 : (p : ZMod q) ≠ 0 := by
    intro h
    simp [h, zero_pow hn0.ne', zero_pow hp.ne_zero] at hroot
  have hne : (p : ZMod q) ^ n ≠ 1 := by
    intro h
    exact hp0 (by simpa [h] using hsum)
  have hdvd : p ∣ q - 1 := by
    rw [← orderOf_eq_prime hroot hne]
    exact ZMod.orderOf_dvd_card_sub_one (pow_ne_zero _ hp0)
  have hq1 : (q : ZMod p) = 1 := by
    rw [← Nat.cast_one]
    exact (ZMod.natCast_eq_natCast_iff q 1 p).2 ((Nat.modEq_iff_dvd' hq.pos).2 hdvd).symm
  have hsq : IsSquare (p : ZMod q) := by
    -- If n * p = 2 * k + 1, then squaring p ^ (k + 1) gives p ^ (n * p) * p = p.
    obtain ⟨k, hk⟩ := hn.mul (hp.odd_of_ne_two (by omega))
    refine ⟨(p : ZMod q) ^ (k + 1), ?_⟩
    rw [← pow_two, ← pow_mul, show (k + 1) * 2 = n * p + 1 by omega, pow_succ,
      pow_mul, hroot, one_mul]
  intro hq4
  have hpq : p ≠ q := by
    rintro rfl
    exact hp0 (ZMod.natCast_self p)
  exact (ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three hp4 hq4 hpq).mp
    (hq1 ▸ IsSquare.one) hsq

/-- **Geometric sums for primes $p \equiv 3 \pmod 4$ and odd $n$ are sums of two squares.**
Let $p$ be a prime with $p \equiv 3 \pmod 4$, let $n$ be a positive odd integer, and let
$S = \sum_{j=0}^{p-1} p^{nj} = 1 + p^n + p^{2n} + \cdots + p^{(p-1)n}$. Then every prime divisor
of $S$ is $2$ or congruent to $1$ modulo $4$, and there are natural numbers $a, b$ with
$S = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 10. -/
public theorem geomSum_pythagorean (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) :
    (∀ q : ℕ, q.Prime →
      q ∣ ∑ j ∈ Finset.range p, p ^ (n * j) → q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ, ∑ j ∈ Finset.range p, p ^ (n * j) = a ^ 2 + b ^ 2 := by
  have hdiv {q : ℕ} := prime_divisor_mod_four_ne_three (q := q) hp hp4 hn hn0
  constructor
  · intro q hq hd
    rcases hq.eq_two_or_odd with h | h
    · exact Or.inl h
    · have := hdiv hq hd
      exact Or.inr (by omega)
  · apply Nat.eq_sq_add_sq_iff.mpr
    intro q hq hq4
    exact (hdiv (Nat.prime_of_mem_primeFactors hq) (Nat.dvd_of_mem_primeFactors hq) hq4).elim

/-- **Geometric sums with $p^k$ terms, $p \equiv 3 \pmod 4$ and $n$ odd, are sums of two squares.**
Let $p$ be a prime with $p \equiv 3 \pmod 4$, let $n$ be a positive odd integer, let $k$ be a
positive integer, and put $q = p^k$. Then there are integers $a, b$ with
$\sum_{j=0}^{q-1} p^{nj} = 1 + p^n + p^{2n} + \cdots + p^{(q-1)n} = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 11. -/
public theorem geomSumPow_eq_sq_add_sq (p n k : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) (hk : 1 ≤ k) :
    ∃ a b : ℤ, (∑ j ∈ Finset.range (p ^ k), (p : ℤ) ^ (n * j)) =
      a ^ 2 + b ^ 2 := by
  have hk0 : 0 ≤ k := (Nat.zero_le 1).trans hk
  clear hk
  have hpOdd := hp.odd_of_ne_two (by omega)
  have hp1 : 1 < (p : ℤ) := by exact_mod_cast hp.one_lt
  have hx : (p : ℤ) ^ n - 1 ≠ 0 := sub_ne_zero.mpr (one_lt_pow₀ hp1 hn0.ne').ne'
  induction k, hk0 using Nat.le_induction with
  | base => exact ⟨1, 0, by simp⟩
  | succ k _ ih =>
    obtain ⟨a, b, hab⟩ := ih
    obtain ⟨c, d, hcd⟩ := (geomSum_pythagorean p (n * p ^ k) hp hp4
      (hn.mul (hpOdd.pow)) (Nat.mul_pos hn0 (pow_pos hp.pos _))).2
    have hcd' : (∑ j ∈ Finset.range p, (p : ℤ) ^ ((n * p ^ k) * j)) =
        (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hcd
    have hfactor : (∑ j ∈ Finset.range (p ^ (k + 1)), (p : ℤ) ^ (n * j)) =
        (∑ j ∈ Finset.range (p ^ k), (p : ℤ) ^ (n * j)) *
          (∑ j ∈ Finset.range p, (p : ℤ) ^ ((n * p ^ k) * j)) := by
      rw [pow_succ p k]
      simp only [pow_mul]
      -- Multiplying by `p ^ n - 1` telescopes the geometric sums.
      apply mul_right_cancel₀ hx
      rw [geom_sum_mul, mul_right_comm, geom_sum_mul, mul_geom_sum, pow_mul]
    refine ⟨a * (c : ℤ) - b * (d : ℤ), a * (d : ℤ) + b * (c : ℤ), ?_⟩
    rw [hfactor, hab, hcd']
    ring

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted
