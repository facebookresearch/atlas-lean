/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Int.Basic

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Alternating geometric sums as sums of coprime squares

For coprime integers $x, y$ and $n > 0$, the sum with $2n+1$ terms
$\sum_{j=0}^{2n} (-1)^j x^{4n-2j} y^{2j}$ is a sum of two coprime natural-number
squares, and every prime divisor is `2` or congruent to `1` modulo `4`.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and Franz Lemmermeyer,
"Geometric Sums as Sums of Two Squares", *INTEGERS* 26 (2026), Article A30
(<https://math.colgate.edu/~integers/vol26.html>).
-/

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

private def bigeom (u v : ℤ) (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range k, u ^ j * v ^ (k - 1 - j)

private theorem bigeom_succ (u v : ℤ) (k : ℕ) :
    bigeom u v (k + 1) = u ^ k + v * bigeom u v k := by
  simpa only [bigeom, Nat.add_sub_cancel] using geom_sum₂_succ_eq u v (n := k)

private theorem bigeom_comm (u v : ℤ) (k : ℕ) :
    bigeom u v k = bigeom v u k := geom_sum₂_comm u v k

private theorem bigeom_coprime_right (u v : ℤ) (k : ℕ) (huv : IsCoprime u v) :
    IsCoprime (bigeom u v (k + 1)) v := by
  rw [bigeom_succ]
  exact huv.pow_left.add_mul_left_left _

private theorem bigeom_coprime (u v : ℤ) (k : ℕ) (huv : IsCoprime u v) (hk : 0 < k) :
    IsCoprime (bigeom u v (k + 1)) (bigeom u v k) := by
  have hc : IsCoprime (bigeom u v k) u := by
    rw [bigeom_comm, show k = (k - 1) + 1 by omega]
    exact bigeom_coprime_right v u (k - 1) huv.symm
  rw [bigeom_succ]
  exact hc.symm.pow_left.add_mul_right_left _

private theorem bigeom_double (u v : ℤ) (k : ℕ) (huv : u ≠ v) :
    bigeom u v (2 * k + 1) =
      bigeom u v (k + 1) ^ 2 - u * v * bigeom u v k ^ 2 := by
  have hm (m : ℕ) : bigeom u v m * (u - v) = u ^ m - v ^ m :=
    geom_sum₂_mul u v m
  apply mul_right_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr huv))
  calc
    bigeom u v (2 * k + 1) * (u - v) ^ 2 =
        (u ^ (2 * k + 1) - v ^ (2 * k + 1)) * (u - v) := by
      rw [pow_two, ← mul_assoc, hm]
    _ = (u ^ (k + 1) - v ^ (k + 1)) ^ 2 -
        u * v * (u ^ k - v ^ k) ^ 2 := by
      simp only [pow_succ, pow_mul]
      ring
    _ = (bigeom u v (k + 1) ^ 2 - u * v * bigeom u v k ^ 2) * (u - v) ^ 2 := by
      rw [← hm, ← hm]
      ring

private theorem alternating_eq (x y : ℤ) (n : ℕ) :
    (∑ j ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ j * x ^ (4 * n - 2 * j) * y ^ (2 * j)) =
        bigeom (-(y ^ 2)) (x ^ 2) (2 * n + 1) := by
  unfold bigeom
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ 2 * n := by
    have := Finset.mem_range.mp hj
    omega
  have he : 4 * n - 2 * j = 2 * (2 * n - j) := by omega
  rw [he, show -(y ^ 2) = (-1 : ℤ) * y ^ 2 by ring]
  simp only [Nat.add_sub_cancel, mul_pow, pow_mul]
  ring

/-- **An alternating sum in coprime integers $x, y$ is a sum of two coprime squares.**
Let $x$ and $y$ be coprime integers, let $n$ be a positive integer, and let
$S = \sum_{j=0}^{2n} (-1)^j x^{4n-2j} y^{2j}$, that is,
$S = x^{4n} - x^{4n-2} y^2 + \cdots - x^2 y^{4n-2} + y^{4n}$. Then every prime divisor of $S$ is
$2$ or congruent to $1$ modulo $4$, and there are coprime natural numbers $a, b$ with
$S = a^2 + b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Theorem 6. -/
public theorem altBigeom_pythagorean (x y : ℤ) (n : ℕ)
    (hxy : IsCoprime x y) (hn : 0 < n) :
    (∀ q : ℕ, q.Prime →
      (q : ℤ) ∣ ∑ j ∈ Finset.range (2 * n + 1),
        (-1 : ℤ) ^ j * x ^ (4 * n - 2 * j) * y ^ (2 * j) →
        q = 2 ∨ q % 4 = 1) ∧
      ∃ a b : ℕ,
        (∑ j ∈ Finset.range (2 * n + 1),
          (-1 : ℤ) ^ j * x ^ (4 * n - 2 * j) * y ^ (2 * j)) =
          (a : ℤ) ^ 2 + (b : ℤ) ^ 2 ∧ Nat.Coprime a b := by
  let u : ℤ := -(y ^ 2)
  let v : ℤ := x ^ 2
  let A := bigeom u v (n + 1)
  let C := bigeom u v n
  let B := x * y * C
  have huv : IsCoprime u v := hxy.symm.pow.neg_left
  have huv_ne : u ≠ v := by
    intro h
    have hx : x = 0 := by
      dsimp [u, v] at h
      nlinarith [sq_nonneg y]
    have hy : y = 0 := by
      dsimp [u, v] at h
      nlinarith [sq_nonneg x]
    exact not_isCoprime_zero_zero (hx ▸ hy ▸ hxy)
  have hAx : IsCoprime A x := by
    have h := bigeom_coprime_right u v n huv
    exact (IsCoprime.pow_right_iff (by omega)).mp h
  have hAy : IsCoprime A y := by
    have h := bigeom_coprime_right v u n huv.symm
    rw [← bigeom_comm] at h
    have h' : IsCoprime A (y ^ 2) := by
      simpa only [u, neg_neg] using h.neg_right
    exact (IsCoprime.pow_right_iff (by omega)).mp h'
  have hAC : IsCoprime A C := bigeom_coprime u v n huv hn
  have hAB : IsCoprime A B := (hAx.mul_right hAy).mul_right hAC
  have hs : (∑ j ∈ Finset.range (2 * n + 1),
      (-1 : ℤ) ^ j * x ^ (4 * n - 2 * j) * y ^ (2 * j)) = A ^ 2 + B ^ 2 := by
    rw [alternating_eq, bigeom_double _ _ _ huv_ne]
    dsimp [A, B, C, u, v]
    ring
  constructor
  · intro q hq hd
    have : Fact q.Prime := ⟨hq⟩
    have hsq := ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_isCoprime hs hAB
    have hq4 : q % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp
      (ZMod.isSquare_neg_one_of_dvd (Int.natCast_dvd.mp hd) hsq)
    rcases hq.eq_two_or_odd with h | h
    · exact Or.inl h
    · exact Or.inr (by omega)
  · refine ⟨A.natAbs, B.natAbs, ?_, Int.isCoprime_iff_nat_coprime.mp hAB⟩
    simpa only [Int.natCast_natAbs, sq_abs] using hs

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted
