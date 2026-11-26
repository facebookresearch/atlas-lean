/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.GibonacciPolynomialInverseRatio
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Gibonacci polynomial square sums at shifted even multiples of the index

The generalized Catalan identity writes each summand as the difference of two inverse ratios
at consecutive odd multiples of the index; their telescoping sum is the infinite sum.

Statements from Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.2.
-/

namespace MetaMathlibExt

open Polynomial

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `l_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

/-- **Gibonacci polynomial square sums at shifted even multiples of the index.** Let $f_n$ and
$l_n$ denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$,
$l_1 = x$ and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number
$x > 0$, and let $\beta = (x - \sqrt{x^2 + 4})/2$. Let $g$ be $f$ with $(\mu, \nu) = (1, -1)$, or
$l$ with $(\mu, \nu) = (x^2 + 4, 1)$. Then for every positive integer $k$ and every natural
number $r$,
$$\sum_{n \ge 1} \frac{(-1)^k \mu \nu f_r f_{2k}}{g_{2nk+r}^2 + (-1)^{r+k} \mu \nu f_k^2}
= \frac{g_k}{g_{k+r}} - (-\beta)^r.$$

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.2. -/
public theorem tsum_fib_mul_div_gibonacciPoly_shift_sq_add {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} {μ ν : ℝ}
    (hg : (g = 𝔣 ∧ μ = 1 ∧ ν = -1) ∨ (g = 𝔩 ∧ μ = x ^ 2 + 4 ∧ ν = 1)) {k : ℕ} (hk : 0 < k)
    (r : ℕ) :
    ∑' n : ℕ, (-1) ^ k * μ * ν * aeval x (𝔣 r) * aeval x (𝔣 (2 * k)) /
        (aeval x (g (2 * (n + 1) * k + r)) ^ 2 + (-1) ^ (r + k) * μ * ν * aeval x (𝔣 k) ^ 2) =
      aeval x (g k) / aeval x (g (k + r)) - (-((x - √(x ^ 2 + 4)) / 2)) ^ r := by
  let G (j : ℕ) := aeval x (g j)
  let F (j : ℕ) := aeval x (𝔣 j)
  have hG (j : ℕ) : G (j + 2) = x * G (j + 1) + 1 * G j := by
    rcases hg with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> simp [G]
  have hF (j : ℕ) : F (j + 2) = x * F (j + 1) + 1 * F j := by simp [F]
  have hseeds : 0 ≤ G 0 ∧ 0 < G 1 ∧ G 1 * G 1 - G 0 * G 2 = -(μ * ν) := by
    rcases hg with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
      norm_num [G, generalizedFibonacciPolynomial, hx, map_ofNat]
    ring
  have hpos' (j : ℕ) : 0 ≤ G j ∧ 0 < G (j + 1) := by
    induction j with
    | zero => exact ⟨hseeds.1, hseeds.2.1⟩
    | succ j ih =>
      refine ⟨ih.2.le, ?_⟩
      rw [hG j, one_mul]
      exact add_pos_of_pos_of_nonneg (mul_pos hx ih.2) ih.1
  have hpos (j : ℕ) (hj : 0 < j) : 0 < G j := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
    exact (hpos' j).2
  have catalan := horadam_generalized_catalan_identity x 1 G G F hG hG hF
    (by simp [F]) (by simp [F])
  have det (s i j : ℕ) :
      G (s + i) * G (s + j) - G s * G (s + i + j) =
        (-1) ^ s * (-(μ * ν)) * F j * F i := by
    have hseed := catalan 0 j 1
    simp only [Nat.zero_add, pow_zero, one_mul, mul_comm (G j) (G 1), hseeds.2.2] at hseed
    rw [catalan, hseed]
    ring
  let m (n : ℕ) := (2 * n + 1) * k
  let c := (-1 : ℝ) ^ k * μ * ν * F r * F (2 * k)
  let d (n : ℕ) := G (2 * (n + 1) * k + r) ^ 2 + (-1 : ℝ) ^ (r + k) * μ * ν * F k ^ 2
  have hm (n : ℕ) : 0 < m n := Nat.mul_pos (by omega) hk
  have hnext (n : ℕ) : m (n + 1) = m n + 2 * k := by dsimp [m]; ring
  have hsign (n : ℕ) : (-1 : ℝ) ^ m n = (-1) ^ k := by
    simp [m, Nat.add_mul, pow_add, Nat.mul_assoc, pow_mul]
  have hsignshift (n : ℕ) : (-1 : ℝ) ^ (m n + r) = (-1) ^ (r + k) := by
    rw [pow_add, hsign n, ← pow_add, Nat.add_comm k]
  have hden (n : ℕ) : d n = G (m n + r) * G (m (n + 1) + r) := by
    have h := det (m n + r) k k
    rw [hsignshift] at h
    dsimp only [d]
    rw [show 2 * (n + 1) * k + r = m n + r + k by dsimp [m]; ring, hnext,
      show m n + 2 * k + r = m n + r + k + k by omega]
    linear_combination h
  have hdiff (n : ℕ) :
      c / d n = G (m n) / G (m n + r) - G (m (n + 1)) / G (m (n + 1) + r) := by
    have hpos1 : 0 < m n + r := Nat.add_pos_left (hm n) r
    have hpos2 : 0 < m (n + 1) + r := Nat.add_pos_left (hm (n + 1)) r
    rw [hden, div_sub_div _ _ (hpos _ hpos1).ne' (hpos _ hpos2).ne']
    congr 1
    rw [hnext]
    have h := det (m n) (2 * k) r
    rw [hsign] at h
    simp only [c]
    linear_combination h
  have hg' : g = 𝔣 ∨ g = 𝔩 := by
    rcases hg with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  have htel := tsum_gibonacciPoly_pow_inv_ratio_telescope hx hg' hk r 1
  change ∑' n, c / d n = _
  simp_rw [hdiff]
  simpa [G, m, pow_one, show ∀ n : ℕ, 2 * (n + 1) + 1 = 2 * n + 3 by omega] using htel

end MetaMathlibExt
