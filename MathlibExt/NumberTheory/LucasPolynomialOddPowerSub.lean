/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities

/-!
# Differences of odd powers of Lucas polynomials

For natural numbers `k ≤ n` and `m`, the difference of the `(2m + 1)`st powers of the
Lucas polynomials at indices `n + k` and `n - k` expands into products of Lucas polynomials
when `k` is odd, or products of Fibonacci polynomials multiplied by `X ^ 2 + 4` when
`k` is even. The source assumes `k > 0`; the identity also holds for `k = 0`, since the
left side then cancels and each term on the right contains the zero Fibonacci polynomial.

At each real evaluation point, pair complementary terms of the binomial expansion of the
Lucas Binet formula. The product of the two roots is `-1`, which gives the common sign
and factors the difference of the shifted root traces. Equality at every real argument
then gives equality in `ℤ[X]`.

## References

* Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
  The Fibonacci Quarterly 62 (2024), no. 2, 147–156, Lemma 4.2 (p. 154).
* Thomas Koshy, *Fibonacci and Lucas Numbers with Applications*, vol. 2,
  John Wiley & Sons, 2019, §31.1 (Binet formulas, cited in Lin and Zhou, §2).
* The real Binet step uses `generalizedFibonacci_binet` from
  `MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities`. The complementary-index
  and root-shift arguments adapt `sub_pow_odd_pair` and `root_diff_shift` from
  `MathlibExt.NumberTheory.FibonacciPolynomialOddPowerSub`. The polynomial descent follows
  `fibPoly_pow_even_sub` from
  `MathlibExt.NumberTheory.GibonacciPolynomialPowerSumsFibPolyPowEvenSub`.
-/

namespace MetaMathlibExt

open Polynomial

local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

private theorem add_pow_odd_pair {R : Type*} [CommSemiring R] (a b : R) (m : ℕ) :
    (a + b) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : R) * (a * b) ^ j *
        (a ^ (2 * m + 1 - 2 * j) + b ^ (2 * m + 1 - 2 * j)) := by
  rw [add_pow]
  let f (j : ℕ) : R := a ^ j * b ^ (2 * m + 1 - j) * (2 * m + 1).choose j
  change ∑ j ∈ Finset.range (2 * m + 1 + 1), f j = _
  rw [show 2 * m + 1 + 1 = (m + 1) + (m + 1) by omega, Finset.sum_range_add,
    ← Finset.sum_range_reflect (fun j ↦ f (m + 1 + j)), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  let d := 2 * m + 1 - 2 * j
  have hsplit : 2 * m + 1 - j = j + d := by dsimp [d]; omega
  rw [show m + 1 + (m + 1 - 1 - j) = 2 * m + 1 - j by omega]
  dsimp only [f]
  rw [show 2 * m + 1 - (2 * m + 1 - j) = j by omega,
    Nat.choose_symm (by omega : j ≤ 2 * m + 1), hsplit, pow_add, pow_add, mul_pow]
  ring

-- The two cross terms recover the trace at the smaller index.
private theorem root_trace_shift {R : Type*} [CommRing R] {a b : R} (hab : a * b = -1)
    {n k : ℕ} (hk : k ≤ n) :
    (a ^ (n + k) + b ^ (n + k)) - (a ^ (n - k) + b ^ (n - k)) =
      (a ^ n - (-1) ^ k * b ^ n) * (a ^ k - (-1) ^ k * b ^ k) := by
  have cross (u v : R) (huv : u * v = -1) :
      (-1) ^ k * (u ^ n * v ^ k) = u ^ (n - k) := by
    calc
      _ = (-1) ^ k * (u ^ (n - k) * u ^ k * v ^ k) := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      _ = u ^ (n - k) * ((-1) * (u * v)) ^ k := by simp only [mul_pow]; ring
      _ = _ := by rw [huv, neg_one_mul, neg_neg, one_pow, mul_one]
  have hsign : ((-1 : R) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_comm k 2]
    exact (even_two_mul k).neg_one_pow
  rw [pow_add a, pow_add b]
  linear_combination cross a b hab + cross b a (by rwa [mul_comm]) - b ^ n * b ^ k * hsign

private theorem lucas_pow_odd_sub_eval (x : ℝ) {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → aeval x (𝔩 (n + k)) ^ (2 * m + 1) - aeval x (𝔩 (n - k)) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ ((n + 1) * j) *
        aeval x (𝔩 (n * (2 * m + 1 - 2 * j))) * aeval x (𝔩 (k * (2 * m + 1 - 2 * j)))) ∧
    (Even k → aeval x (𝔩 (n + k)) ^ (2 * m + 1) - aeval x (𝔩 (n - k)) ^ (2 * m + 1) =
      (x ^ 2 + 4) * ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ (n * j) *
        aeval x (𝔣 (n * (2 * m + 1 - 2 * j))) * aeval x (𝔣 (k * (2 * m + 1 - 2 * j)))) := by
  let F (r : ℕ) : ℝ := aeval x (𝔣 r)
  let L (r : ℕ) : ℝ := aeval x (𝔩 r)
  let s := Real.sqrt (x ^ 2 + 4)
  let a := (x + s) / 2
  let b := (x - s) / 2
  let d (j : ℕ) := 2 * m + 1 - 2 * j
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hs₂ : s ^ 2 = x ^ 2 + 4 := Real.sq_sqrt (by positivity)
  have hab : a * b = -1 := by dsimp only [a, b]; linear_combination -hs₂ / 4
  have hrec (p q : ℤ[X]) (r : ℕ) :
      aeval x (generalizedFibonacciPolynomial p q X 1 (r + 2)) =
        x * aeval x (generalizedFibonacciPolynomial p q X 1 (r + 1)) +
          aeval x (generalizedFibonacciPolynomial p q X 1 r) := by simp
  have hF (r : ℕ) : a ^ r - b ^ r = s * F r := by
    have h := generalizedFibonacci_binet x F (hrec 0 1) r
    change F r = (F 1 - F 0 * b) / s * a ^ r + (F 0 * a - F 1) / s * b ^ r at h
    have h₀ : F 0 = 0 := by simp [F]
    have h₁ : F 1 = 1 := by simp [F]
    have hf : F r = (a ^ r - b ^ r) / s := by rw [h, h₀, h₁]; ring
    simpa only [mul_comm] using ((eq_div_iff hs).mp hf).symm
  have hL (r : ℕ) : L r = a ^ r + b ^ r := by
    have h := generalizedFibonacci_binet x L (hrec 2 X) r
    change L r = (L 1 - L 0 * b) / s * a ^ r + (L 0 * a - L 1) / s * b ^ r at h
    have h₀ : L 0 = 2 := by simp [L, map_ofNat]
    have h₁ : L 1 = x := by simp [L]
    have hb : x - 2 * b = s := by dsimp only [b]; ring
    have ha : 2 * a - x = s := by dsimp only [a]; ring
    simpa only [h₀, h₁, hb, ha, div_self hs, one_mul] using h
  have hexpand (r : ℕ) : L r ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ (r * j) *
        L (r * d j) := by
    rw [hL r, add_pow_odd_pair]
    apply Finset.sum_congr rfl
    intro j _
    rw [← mul_pow a b r, hab, ← pow_mul, hL, pow_mul a, pow_mul b]
  have hsign : (-1 : ℝ) ^ (n - k) = (-1) ^ (n + k) := by
    rw [show n + k = (n - k) + 2 * k by omega, pow_add, (even_two_mul k).neg_one_pow, mul_one]
  have hsum : L (n + k) ^ (2 * m + 1) - L (n - k) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℝ) * (-1) ^ ((n + k) * j) *
        (L ((n + k) * d j) - L ((n - k) * d j)) := by
    rw [hexpand, hexpand, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_mul _ (n - k), hsign, ← pow_mul, ← mul_sub]
  have hshift (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      L ((n + k) * d j) - L ((n - k) * d j) =
        (a ^ (n * d j) - (-1) ^ k * b ^ (n * d j)) *
          (a ^ (k * d j) - (-1) ^ k * b ^ (k * d j)) := by
    have hj' := Finset.mem_range.mp hj
    have hd : Odd (d j) := ⟨m - j, by dsimp only [d]; omega⟩
    have hparity : (-1 : ℝ) ^ (k * d j) = (-1) ^ k := by
      rw [Nat.mul_comm, pow_mul, hd.neg_one_pow]
    simpa only [hL, ← Nat.add_mul, ← Nat.sub_mul, hparity] using
      root_trace_shift hab (Nat.mul_le_mul_right (d j) hk)
  constructor
  · intro ho
    change L (n + k) ^ (2 * m + 1) - L (n - k) ^ (2 * m + 1) = _
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j hj
    have hs' : (-1 : ℝ) ^ (n + k) = (-1) ^ (n + 1) := by rw [pow_add, ho.neg_one_pow, pow_succ]
    rw [hshift j hj, pow_mul _ (n + k), hs', ← pow_mul, ho.neg_one_pow, neg_one_mul,
      neg_one_mul, sub_neg_eq_add, sub_neg_eq_add, ← hL, ← hL]
    change _ = _ * _ * L (n * d j) * L (k * d j)
    rw [mul_assoc (((2 * m + 1).choose j : ℝ) * (-1) ^ ((n + 1) * j))]
  · intro he
    change L (n + k) ^ (2 * m + 1) - L (n - k) ^ (2 * m + 1) = _
    rw [hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hs' : (-1 : ℝ) ^ (n + k) = (-1) ^ n := by rw [pow_add, he.neg_one_pow, mul_one]
    rw [hshift j hj, pow_mul _ (n + k), hs', ← pow_mul, he.neg_one_pow, one_mul, one_mul, hF, hF,
      ← hs₂]
    change _ = _ * (_ * _ * F (n * d j) * F (k * d j))
    ring

/-- **Odd powers of Lucas polynomials at $n \pm k$.** Let $f_i$ and $\ell_i$ be the
Fibonacci and Lucas polynomials in $\mathbb{Z}[x]$, defined by $f_0 = 0$, $f_1 = 1$, $\ell_0 = 2$,
$\ell_1 = x$ and $g_{i+2} = x g_{i+1} + g_i$ for $g = f, \ell$. Let $k \le n$ and $m$ be natural
numbers. In $\mathbb{Z}[x]$, if $k$ is odd then
$$
\ell_{n+k}^{2m+1} - \ell_{n-k}^{2m+1} =
\sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{(n+1)j} \ell_{n(2m+1-2j)} \ell_{k(2m+1-2j)},
$$
and if $k$ is even then
$$
\ell_{n+k}^{2m+1} - \ell_{n-k}^{2m+1} =
(x^2 + 4) \sum_{j=0}^{m} \binom{2m+1}{j} (-1)^{nj} f_{n(2m+1-2j)} f_{k(2m+1-2j)}.
$$

Source: Yinqi Lin and Bo Zhou, *Infinite Sums Involving Powers of Gibonacci Polynomials*,
The Fibonacci Quarterly 62 (2024), Article linzhou02172024,
Lemma 4.2 (`fq-2024-linzhou02172024-lem-4.2`). -/
public theorem lucasPoly_pow_odd_sub {n k : ℕ} (hk : k ≤ n) (m : ℕ) :
    (Odd k → 𝔩 (n + k) ^ (2 * m + 1) - 𝔩 (n - k) ^ (2 * m + 1) =
      ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) * (-1) ^ ((n + 1) * j) *
        𝔩 (n * (2 * m + 1 - 2 * j)) * 𝔩 (k * (2 * m + 1 - 2 * j))) ∧
    (Even k → 𝔩 (n + k) ^ (2 * m + 1) - 𝔩 (n - k) ^ (2 * m + 1) =
      (X ^ 2 + 4) * ∑ j ∈ Finset.range (m + 1), ((2 * m + 1).choose j : ℤ[X]) *
        (-1) ^ (n * j) * 𝔣 (n * (2 * m + 1 - 2 * j)) * 𝔣 (k * (2 * m + 1 - 2 * j))) := by
  rcases eq_or_ne k 0 with rfl | _
  · simp
  constructor <;> intro hparity <;>
    apply Polynomial.map_injective (algebraMap ℤ ℝ) Int.cast_injective <;>
    apply Polynomial.funext <;> intro x <;> simp only [eval_map, ← aeval_def]
  · simpa only [map_pow, map_sub, map_sum, map_mul, map_natCast, map_neg, map_one] using
      (lucas_pow_odd_sub_eval x hk m).1 hparity
  · simpa only [map_pow, map_sub, map_sum, map_mul, map_natCast, map_neg, map_one, map_add,
      aeval_X, map_ofNat] using (lucas_pow_odd_sub_eval x hk m).2 hparity

end MetaMathlibExt
