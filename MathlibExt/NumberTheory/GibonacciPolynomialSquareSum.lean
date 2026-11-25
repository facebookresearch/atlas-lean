/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Tactic.LinearCombination
import MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities
import MathlibExt.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity

/-!
# Gibonacci polynomial square sums at even multiples

The generalized Catalan identity writes each summand as the difference of two ratios
at consecutive odd multiples of the index. Their limit gives the infinite sum.
-/

namespace MetaMathlibExt

open Filter Polynomial
open scoped Topology

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

namespace GibonacciPolynomialSquareSum

/-- Multiply consecutive ratios along an unbounded sequence of positive indices. -/
private theorem tendsto_shift_ratio {G : ℕ → ℝ} {α : ℝ}
    (hpos : ∀ j, 0 < j → 0 < G j)
    (hlim : Tendsto (fun j => G (j + 1) / G j) atTop (𝓝 α))
    {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) (hmpos : ∀ n, 0 < m n) (r : ℕ) :
    Tendsto (fun n => G (m n + r) / G (m n)) atTop (𝓝 (α ^ r)) := by
  induction r with
  | zero =>
    simp [div_self (hpos _ (hmpos _)).ne']
  | succ r ih =>
    rw [pow_succ']
    have hstep := hlim.comp ((tendsto_add_atTop_nat r).comp hm)
    apply (hstep.mul ih).congr
    intro n
    change G (m n + r + 1) / G (m n + r) * (G (m n + r) / G (m n)) = _
    have hj : 0 < m n + r := Nat.add_pos_left (hmpos n) r
    rw [div_mul_div_cancel₀ (hpos _ hj).ne', Nat.add_assoc]

/-- A real series with a fixed-sign numerator and positive denominators has its
ordinary partial-sum limit as its unconditional sum. -/
private theorem hasSum_div_of_tendsto {c s : ℝ} {d : ℕ → ℝ} (hd : ∀ n, 0 < d n)
    (h : Tendsto (fun N => ∑ n ∈ Finset.range N, c / d n) atTop (𝓝 s)) :
    HasSum (fun n => c / d n) s := by
  rcases le_total 0 c with hc | hc
  · exact (hasSum_iff_tendsto_nat_of_nonneg (fun n => div_nonneg hc (hd n).le) s).2 h
  · have hneg : HasSum (fun n => -(c / d n)) (-s) := by
      apply (hasSum_iff_tendsto_nat_of_nonneg
        (fun n => neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hc (hd n).le)) _).2
      simpa only [Finset.sum_neg_distrib] using h.neg
    simpa using hneg.neg

end GibonacciPolynomialSquareSum

open GibonacciPolynomialSquareSum

/-- **Gibonacci polynomial square sums at even multiples of the index.** Let $f_n$ and $l_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$
and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and
let $\alpha = (x + \sqrt{x^2 + 4})/2$. Let $g$ be $f$ with $(\mu, \nu) = (1, -1)$, or $l$ with
$(\mu, \nu) = (x^2 + 4, 1)$. Then for every positive integer $k$ and every natural number $r$,
$$\sum_{n \ge 1} \frac{(-1)^{k+1} \mu \nu f_r f_{2k}}{g_{2nk}^2 + (-1)^k \mu \nu f_k^2}
= \frac{g_{k+r}}{g_k} - \alpha^r.$$

The extracted statement of this theorem prints the numerator with $(-1)^k$ in place of
$(-1)^{k+1}$, which negates the left side and makes the identity false (for $x = 1$, $g = f$ and
$k = r = 1$ that left side is $(\sqrt{5} - 1)/2$ while the right side is $(1 - \sqrt{5})/2$); the
paper's proof and its corollaries use the sign stated here.

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Theorem 3.1. -/
public theorem tsum_fib_mul_div_gibonacciPoly_sq_add {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} {μ ν : ℝ}
    (hg : (g = 𝔣 ∧ μ = 1 ∧ ν = -1) ∨ (g = 𝔩 ∧ μ = x ^ 2 + 4 ∧ ν = 1)) {k : ℕ} (hk : 0 < k)
    (r : ℕ) :
    ∑' n : ℕ, (-1) ^ (k + 1) * μ * ν * aeval x (𝔣 r) * aeval x (𝔣 (2 * k)) /
        (aeval x (g (2 * (n + 1) * k)) ^ 2 + (-1) ^ k * μ * ν * aeval x (𝔣 k) ^ 2) =
      aeval x (g (k + r)) / aeval x (g k) - ((x + √(x ^ 2 + 4)) / 2) ^ r := by
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
  -- The initial determinant contributes the same factor for every shift.
  have det (s i j : ℕ) :
      G (s + i) * G (s + j) - G s * G (s + i + j) =
        (-1) ^ s * (-(μ * ν)) * F j * F i := by
    have hseed := catalan 0 j 1
    simp only [Nat.zero_add, pow_zero, one_mul, mul_comm (G j) (G 1), hseeds.2.2] at hseed
    rw [catalan, hseed]
    ring
  let m (n : ℕ) := (2 * n + 1) * k
  let R (n : ℕ) := G (m n + r) / G (m n)
  let c := (-1 : ℝ) ^ (k + 1) * μ * ν * F r * F (2 * k)
  let d (n : ℕ) := G (2 * (n + 1) * k) ^ 2 + (-1 : ℝ) ^ k * μ * ν * F k ^ 2
  have hm (n : ℕ) : 0 < m n := Nat.mul_pos (by omega) hk
  have hnext (n : ℕ) : m (n + 1) = m n + 2 * k := by dsimp [m]; ring
  have hsign (n : ℕ) : (-1 : ℝ) ^ m n = (-1) ^ k := by
    simp [m, Nat.add_mul, pow_add, Nat.mul_assoc, pow_mul]
  -- Equal shifts factor the denominator. Shifts of r and 2k give the numerator.
  have hden (n : ℕ) : d n = G (m n) * G (m (n + 1)) := by
    have h := det (m n) k k
    rw [hsign] at h
    dsimp only [d]
    rw [show 2 * (n + 1) * k = m n + k by dsimp [m]; ring, hnext,
      show m n + 2 * k = m n + k + k by omega]
    linear_combination h
  have hdiff (n : ℕ) : c / d n = R n - R (n + 1) := by
    dsimp only [R]
    rw [hden, div_sub_div _ _ (hpos _ (hm n)).ne' (hpos _ (hm (n + 1))).ne']
    congr 1
    rw [hnext, show m n + 2 * k + r = m n + r + 2 * k by omega, det, hsign]
    simp only [c, pow_succ]
    ring
  have hlim := generalizedFibonacci_tendsto_ratio x hx G hseeds.1 hseeds.2.1
    (fun j => by simpa using hG j)
  have hmono : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro n
    rw [hnext]
    omega
  have hR := tendsto_shift_ratio hpos hlim hmono.tendsto_atTop hm r
  change ∑' n, c / d n = _
  apply HasSum.tsum_eq
  apply hasSum_div_of_tendsto (fun n => hden n ▸ mul_pos (hpos _ (hm n)) (hpos _ (hm (n + 1))))
  simp_rw [hdiff, Finset.sum_range_sub']
  simpa [R, m, G] using (tendsto_const_nhds (x := R 0)).sub hR

end MetaMathlibExt
