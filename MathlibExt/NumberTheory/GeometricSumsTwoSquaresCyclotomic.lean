/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.ComputeDegree

/-!
# The cyclotomic polynomial $\Phi_{4p^k}$ as a sum of two explicit squares

For an odd prime $p$ and $k \ge 1$, the main result is
`cyclotomicFourMulPow_eq_sq_add_sq`: the cyclotomic polynomial $\Phi_{4p^k}$
is the sum of the squares of the two explicit alternating polynomials
`phi4pX1` and `phi4pY1`, composed with $x^{p^{k-1}}$.
-/

@[expose] public section

open Polynomial

namespace MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

/-- **The alternating polynomial $X_1$.** For a natural number $p$, $X_1$ is the polynomial with
integer coefficients
$$
X_1(x) = \sum_{i=0}^{\lfloor (p+1)/2 \rfloor - 1} (-1)^i x^{p-1-2i}.
$$
For odd $p \ge 5$ this is the even polynomial
$x^{p-1} - x^{p-3} + \dots - (-1)^{(p-1)/2} x^2 + (-1)^{(p-1)/2}$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
noncomputable def phi4pX1 (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((p + 1) / 2),
    (-1 : ℤ) ^ i • X ^ (p - 1 - 2 * i)

/-- **The alternating polynomial $Y_1$.** For a natural number $p$, $Y_1$ is the polynomial with
integer coefficients
$$
Y_1(x) = \sum_{i=0}^{\lfloor (p-1)/2 \rfloor - 1} (-1)^i x^{p-2-2i}.
$$
For odd $p \ge 5$ this is the odd polynomial
$x^{p-2} - x^{p-4} + \dots + (-1)^{(p-1)/2} x^3 - (-1)^{(p-1)/2} x$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 2. -/
noncomputable def phi4pY1 (p : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range ((p - 1) / 2),
    (-1 : ℤ) ^ i • X ^ (p - 2 - 2 * i)

namespace cyclotomicFourMulPow_eq_sq_add_sq

private theorem x1_eq_geom_sum (m : ℕ) :
    phi4pX1 (2 * m + 1) = (-1 : ℤ) ^ m * ∑ j ∈ Finset.range (m + 1), (-X ^ 2 : ℤ[X]) ^ j := by
  have hm1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  unfold phi4pX1
  rw [hm1]
  rw [← Finset.sum_range_reflect (fun i => (-1 : ℤ) ^ i • X ^ (2 * m + 1 - 1 - 2 * i)) (m + 1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hexp : 2 * m + 1 - 1 - 2 * (m + 1 - 1 - i) = 2 * i := by omega
  have hsign : (-1 : ℤ) ^ (m + 1 - 1 - i) = (-1 : ℤ) ^ m * (-1 : ℤ) ^ i := by
    rw [← pow_add]
    apply neg_one_pow_congr
    simp only [Nat.even_iff]
    omega
  have hterm : (-X ^ 2 : ℤ[X]) ^ i = (-1 : ℤ[X]) ^ i * X ^ (2 * i) := by
    rw [show (-X ^ 2 : ℤ[X]) = -(X ^ 2) by ring, neg_pow, ← pow_mul]
  rw [hexp, hsign, hterm]
  simp only [Algebra.smul_def, Polynomial.algebraMap_eq, map_mul, map_pow]
  have hC : (C (-1 : ℤ) : ℤ[X]) = -1 := by simp
  rw [hC]
  ring_nf

private theorem y1_eq_geom_sum (m : ℕ) :
    phi4pY1 (2 * m + 1) =
      (-1 : ℤ[X]) ^ (m + 1) * X * ∑ j ∈ Finset.range m, (-X ^ 2 : ℤ[X]) ^ j := by
  have hm2 : (2 * m + 1 - 1) / 2 = m := by omega
  unfold phi4pY1
  rw [hm2]
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · simp
  · rw [← Finset.sum_range_reflect
      (fun i => (-1 : ℤ) ^ i • X ^ (2 * m + 1 - 2 - 2 * i)) m]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < m := Finset.mem_range.mp hi
    have hle : i ≤ m - 1 := by omega
    have hexp : 2 * m + 1 - 2 - 2 * (m - 1 - i) = 2 * i + 1 := by omega
    have hsign : (-1 : ℤ) ^ (m - 1 - i) = (-1 : ℤ) ^ (m + 1) * (-1 : ℤ) ^ i := by
      rw [← pow_add]
      apply neg_one_pow_congr
      simp only [Nat.even_iff]
      omega
    have hterm : (-X ^ 2 : ℤ[X]) ^ i = (-1 : ℤ[X]) ^ i * X ^ (2 * i) := by
      rw [show (-X ^ 2 : ℤ[X]) = -(X ^ 2) by ring, neg_pow, ← pow_mul]
    rw [hexp, hsign, hterm]
    simp only [Algebra.smul_def, Polynomial.algebraMap_eq, map_mul, map_pow]
    have hC : (C (-1 : ℤ) : ℤ[X]) = -1 := by simp
    rw [hC]
    ring_nf

private theorem base (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Polynomial.cyclotomic (4 * p) ℤ = phi4pX1 p ^ 2 + phi4pY1 p ^ 2 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  subst hm
  have hX := x1_eq_geom_sum m
  have hY := y1_eq_geom_sum m
  have hne : (X ^ 2 + 1 : ℤ[X]) ≠ 0 := by
    have hdeg : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
      compute_degree
      exact one_ne_zero
    intro h
    rw [h] at hdeg
    simp at hdeg
  have hA : (1 + X ^ 2 : ℤ[X]) * ∑ j ∈ Finset.range (m + 1), (-X ^ 2 : ℤ[X]) ^ j
      = 1 - (-X ^ 2 : ℤ[X]) ^ (m + 1) := by
    have h := geom_sum_mul_neg (-(X : ℤ[X]) ^ 2) (m + 1)
    rw [show (1 : ℤ[X]) - -(X ^ 2) = 1 + X ^ 2 by ring, mul_comm] at h
    exact h
  have hB : (1 + X ^ 2 : ℤ[X]) * ∑ j ∈ Finset.range m, (-X ^ 2 : ℤ[X]) ^ j
      = 1 - (-X ^ 2 : ℤ[X]) ^ m := by
    have h := geom_sum_mul_neg (-(X : ℤ[X]) ^ 2) m
    rw [show (1 : ℤ[X]) - -(X ^ 2) = 1 + X ^ 2 by ring, mul_comm] at h
    exact h
  have hXsq : phi4pX1 (2 * m + 1) ^ 2
      = (∑ j ∈ Finset.range (m + 1), (-X ^ 2 : ℤ[X]) ^ j) ^ 2 := by
    have hsign2 : ((-1 : ℤ[X]) ^ m) ^ 2 = 1 := by
      rw [← pow_mul, show m * 2 = 2 * m by ring, pow_mul, neg_one_sq, one_pow]
    rw [hX, mul_pow]
    simp only [Int.cast_neg, Int.cast_one]
    rw [hsign2, one_mul]
  have hYsq : phi4pY1 (2 * m + 1) ^ 2
      = X ^ 2 * (∑ j ∈ Finset.range m, (-X ^ 2 : ℤ[X]) ^ j) ^ 2 := by
    have hsignY : ((-1 : ℤ[X]) ^ (m + 1)) ^ 2 = 1 := by
      rw [← pow_mul, show (m + 1) * 2 = 2 * (m + 1) by ring, pow_mul, neg_one_sq, one_pow]
    rw [hY, mul_pow, mul_pow, hsignY, one_mul]
  have he2 : ((-X ^ 2 : ℤ[X]) ^ m) ^ 2 = (X ^ 2) ^ (2 * m) := by
    rw [← pow_mul, show m * 2 = 2 * m by ring, pow_mul]
    simp [pow_mul]
  have htp : (X : ℤ[X]) ^ (2 * (2 * m + 1)) = X ^ 2 * ((-X ^ 2 : ℤ[X]) ^ m) ^ 2 := by
    rw [he2, ← pow_mul, pow_succ]
    ring
  have hfinal : (1 - (-X ^ 2 : ℤ[X]) ^ (m + 1)) ^ 2
      + X ^ 2 * (1 - (-X ^ 2 : ℤ[X]) ^ m) ^ 2
      = (1 + X ^ 2) * (1 + X ^ (2 * (2 * m + 1))) := by
    rw [pow_succ, htp]
    ring
  have hC : (X ^ 2 + 1 : ℤ[X]) * (phi4pX1 (2 * m + 1) ^ 2 + phi4pY1 (2 * m + 1) ^ 2)
      = X ^ (2 * (2 * m + 1)) + 1 := by
    have h2 : (X ^ 2 + 1 : ℤ[X]) * ((X ^ 2 + 1) *
          (phi4pX1 (2 * m + 1) ^ 2 + phi4pY1 (2 * m + 1) ^ 2))
        = (X ^ 2 + 1) * (X ^ (2 * (2 * m + 1)) + 1) := by
      have e1 : (X ^ 2 + 1 : ℤ[X]) * ((X ^ 2 + 1) *
          (phi4pX1 (2 * m + 1) ^ 2 + phi4pY1 (2 * m + 1) ^ 2))
          = ((1 + X ^ 2) * ∑ j ∈ Finset.range (m + 1), (-X ^ 2 : ℤ[X]) ^ j) ^ 2
            + X ^ 2 * ((1 + X ^ 2) * ∑ j ∈ Finset.range m, (-X ^ 2 : ℤ[X]) ^ j) ^ 2 := by
        rw [hXsq, hYsq]
        ring
      rw [e1, hA, hB, hfinal]
      ring
    exact mul_left_cancel₀ hne h2
  have h2p : Polynomial.cyclotomic (2 * (2 * m + 1)) ℤ * (X + 1 : ℤ[X])
      = X ^ (2 * m + 1) + 1 := by
    have h := Polynomial.cyclotomic_expand_eq_cyclotomic_mul
      hp (show ¬ (2 * m + 1) ∣ 2 by
      intro hd
      have hp3 : 3 ≤ 2 * m + 1 := by have h2 := hp.two_le; omega
      have hle := Nat.le_of_dvd (show 0 < 2 by norm_num) hd
      omega) ℤ
    have hexp : Polynomial.expand ℤ (2 * m + 1) ((X + 1 : ℤ[X])) = X ^ (2 * m + 1) + 1 := by
      simp [Polynomial.expand_eq_comp_X_pow]
    rw [Polynomial.cyclotomic_two, hexp] at h
    exact h.symm
  have h4p : Polynomial.cyclotomic (4 * (2 * m + 1)) ℤ * (X ^ 2 + 1 : ℤ[X])
      = X ^ (2 * (2 * m + 1)) + 1 := by
    have h := Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two
      (dvd_mul_right 2 (2 * m + 1)) ℤ (n := 2 * (2 * m + 1))
    have hmap := congrArg (Polynomial.expand ℤ 2) h2p
    rw [map_mul, h] at hmap
    have hexp2 : Polynomial.expand ℤ 2 ((X + 1 : ℤ[X])) = X ^ 2 + 1 := by
      simp [Polynomial.expand_eq_comp_X_pow]
    have hexp3 : Polynomial.expand ℤ 2 ((X ^ (2 * m + 1) + 1 : ℤ[X]))
        = X ^ (2 * (2 * m + 1)) + 1 := by
      simp [Polynomial.expand_eq_comp_X_pow, pow_mul]
    rw [hexp2, hexp3] at hmap
    have hidx : 2 * (2 * m + 1) * 2 = 4 * (2 * m + 1) := by ring
    rwa [hidx] at hmap
  rw [mul_comm] at h4p
  have hEq : (X ^ 2 + 1 : ℤ[X]) * (phi4pX1 (2 * m + 1) ^ 2 + phi4pY1 (2 * m + 1) ^ 2)
      = (X ^ 2 + 1) * Polynomial.cyclotomic (4 * (2 * m + 1)) ℤ := by
    rw [hC, h4p]
  exact (mul_left_cancel₀ hne hEq).symm

private theorem expand_eq_cyclotomic (p : ℕ) (hp : p.Prime) (j : ℕ) :
    Polynomial.expand ℤ (p ^ j) (Polynomial.cyclotomic (4 * p) ℤ)
      = Polynomial.cyclotomic (4 * p ^ (j + 1)) ℤ := by
  induction j with
  | zero =>
    simp [Polynomial.expand_one]
  | succ j ih =>
    have h1 : p ^ (j + 1) = p * p ^ j := by rw [pow_succ']
    rw [h1, ← Polynomial.expand_expand, ih]
    have h2 : Polynomial.expand ℤ p (Polynomial.cyclotomic (4 * p ^ (j + 1)) ℤ)
        = Polynomial.cyclotomic (4 * p ^ (j + 1) * p) ℤ :=
      Polynomial.cyclotomic_expand_eq_cyclotomic hp (by
        exact ⟨4 * p ^ j, by ring⟩) ℤ
    rw [h2]
    congr 1
    rw [pow_succ]
    ring

end cyclotomicFourMulPow_eq_sq_add_sq

/-- **The cyclotomic polynomial $\Phi_{4p^k}$ as a sum of two explicit squares.** Let $p$ be an
odd prime, let $k \ge 1$, let $X_1 = \sum_{i=0}^{(p-1)/2} (-1)^i x^{p-1-2i}$ and
$Y_1 = \sum_{i=0}^{(p-3)/2} (-1)^i x^{p-2-2i}$ in $\mathbb{Z}[x]$, and let $\Phi_{4p^k}$ be the
$4p^k$-th cyclotomic polynomial over $\mathbb{Z}$. Then
$\Phi_{4p^k}(x) = X_1\bigl(x^{p^{k-1}}\bigr)^2 + Y_1\bigl(x^{p^{k-1}}\bigr)^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Corollary 3. -/
theorem cyclotomicFourMulPow_eq_sq_add_sq (p k : ℕ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) :
    Polynomial.cyclotomic (4 * p ^ k) ℤ =
      (phi4pX1 p).comp (X ^ (p ^ (k - 1))) ^ 2 +
        (phi4pY1 p).comp (X ^ (p ^ (k - 1))) ^ 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hj : 1 + j - 1 = j := by omega
  rw [hj]
  have hbase := cyclotomicFourMulPow_eq_sq_add_sq.base p hp hp2
  have hexp := cyclotomicFourMulPow_eq_sq_add_sq.expand_eq_cyclotomic p hp j
  rw [add_comm (1 : ℕ) j]
  rw [hbase] at hexp
  rw [← hexp]
  simp only [Polynomial.expand_eq_comp_X_pow, map_add, map_pow]

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted
