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
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities

/-!
# Telescoping powers of inverse gibonacci polynomial ratios

The Binet formula expresses the powered ratio at index `n` as a rational function of
`(β / α) ^ n`. Its denominator is nonzero at the origin, so its deviation from its
limiting value is bounded by a summable geometric sequence.
-/

namespace MetaMathlibExt

open Polynomial Filter Asymptotics
open scoped Topology

/-- The Fibonacci polynomials `f_n(x)`. -/
local notation "𝔣" => generalizedFibonacciPolynomial 0 1 X 1

/-- The Lucas polynomials `l_n(x)`. -/
local notation "𝔩" => generalizedFibonacciPolynomial 2 X X 1

namespace GibonacciPolynomialInverseRatio

/-- Errors in powered inverse ratios of a two-root Binet sequence are summable
when its leading coefficient is nonzero and the second root is smaller in modulus. -/
private theorem summable_binet_ratio_sub {u : ℕ → ℝ} {a b c d : ℝ} (ha : a ≠ 0)
    (hc : c ≠ 0) (hq : |b / a| < 1) (hu : ∀ n, u n = c * a ^ n + d * b ^ n)
    (r lam : ℕ) :
    Summable fun n => u n ^ lam / u (n + r) ^ lam - a⁻¹ ^ (r * lam) := by
  let q := b / a
  let F (t : ℝ) := ((c + d * t) / (a ^ r * (c + d * (t * q ^ r)))) ^ lam
  have hfactor (n : ℕ) : u n = a ^ n * (c + d * q ^ n) := by
    rw [hu, show q = b / a from rfl, div_pow]
    field_simp
  have hratio (n : ℕ) : u n ^ lam / u (n + r) ^ lam = F (q ^ n) := by
    rw [← div_pow, hfactor n, hfactor (n + r), pow_add, pow_add, mul_assoc,
      mul_div_mul_left _ _ (pow_ne_zero n ha)]
  have hzero : F 0 = a⁻¹ ^ (r * lam) := by
    simp [F, hc, div_eq_mul_inv, pow_mul]
  have hd : DifferentiableAt ℝ F 0 := by
    dsimp [F]
    fun_prop (disch := simp [hc, ha])
  have hbound : (fun t => F t - F 0) =O[𝓝 0] (fun t => t) := by
    simpa using hd.isBigO_sub
  simp_rw [hratio, ← hzero]
  exact summable_of_isBigO_nat (summable_geometric_of_abs_lt_one hq)
    (hbound.comp_tendsto (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq))

end GibonacciPolynomialInverseRatio

open GibonacciPolynomialInverseRatio

/-- **Telescoping sum of powers of inverse gibonacci polynomial ratios.** Let $f_n$ and $l_n$
denote the Fibonacci and Lucas polynomials, given by $f_0 = 0$, $f_1 = 1$, $l_0 = 2$, $l_1 = x$
and $g_{n+2} = x g_{n+1} + g_n$ for $g \in \{f, l\}$, evaluated at a real number $x > 0$, and
let $\beta = (x - \sqrt{x^2 + 4})/2$. Then for $g \in \{f, l\}$, every positive integer $k$ and
all natural numbers $r$ and $\lambda$,
$$\sum_{n \ge 0} \left(\frac{g_{(2n+1)k}^\lambda}{g_{(2n+1)k+r}^\lambda} -
\frac{g_{(2n+3)k}^\lambda}{g_{(2n+3)k+r}^\lambda}\right)
= \frac{g_k^\lambda}{g_{k+r}^\lambda} - (-\beta)^{r\lambda}.$$

Source: Thomas Koshy, *More Sums Involving Gibonacci Polynomial Squares Revisited*,
The Fibonacci Quarterly 62 (2024), Article koshy07202023, Lemma 2.2. -/
public theorem tsum_gibonacciPoly_pow_inv_ratio_telescope {x : ℝ} (hx : 0 < x)
    {g : ℕ → ℤ[X]} (hg : g = 𝔣 ∨ g = 𝔩) {k : ℕ} (hk : 0 < k) (r lam : ℕ) :
    ∑' n : ℕ, (aeval x (g ((2 * n + 1) * k)) ^ lam / aeval x (g ((2 * n + 1) * k + r)) ^ lam -
        aeval x (g ((2 * n + 3) * k)) ^ lam / aeval x (g ((2 * n + 3) * k + r)) ^ lam) =
      aeval x (g k) ^ lam / aeval x (g (k + r)) ^ lam -
        (-((x - √(x ^ 2 + 4)) / 2)) ^ (r * lam) := by
  let u (n : ℕ) := aeval x (g n)
  have hrec (n : ℕ) : u (n + 2) = x * u (n + 1) + u n := by
    rcases hg with rfl | rfl <;> simp [u]
  let Δ := √(x ^ 2 + 4)
  let α := (x + Δ) / 2
  let β := (x - Δ) / 2
  have hΔ : x < Δ := (Real.lt_sqrt hx.le).2 (by linarith)
  have hα : 0 < α := by dsimp [α]; linarith
  have hβ : β < 0 := by dsimp [β]; linarith
  have hq : |β / α| < 1 := by
    rw [abs_div, abs_of_neg hβ, abs_of_pos hα, div_lt_one hα]
    dsimp [α, β]
    linarith
  have hroots : α⁻¹ = -β := by
    apply inv_eq_of_mul_eq_one_right
    dsimp [α, β, Δ]
    nlinarith [Real.sq_sqrt (show 0 ≤ x ^ 2 + 4 by positivity)]
  have hseeds : 0 ≤ u 0 ∧ 0 < u 1 := by
    rcases hg with rfl | rfl <;> norm_num [u, hx, map_ofNat]
  have hc : 0 < (u 1 - u 0 * β) / Δ := by
    apply div_pos _ (hx.trans hΔ)
    exact sub_pos.mpr ((mul_nonpos_of_nonneg_of_nonpos hseeds.1 hβ.le).trans_lt hseeds.2)
  let R (n : ℕ) := u n ^ lam / u (n + r) ^ lam
  have hsum : Summable fun n => R n - (-β) ^ (r * lam) := by
    rw [← hroots]
    exact summable_binet_ratio_sub hα.ne' hc.ne' hq (generalizedFibonacci_binet x u hrec) r lam
  let e (n : ℕ) := R ((2 * n + 1) * k) - (-β) ^ (r * lam)
  have he : Summable e := by
    apply hsum.comp_injective (i := fun n : ℕ => (2 * n + 1) * k)
    intro i j hij
    have := Nat.eq_of_mul_eq_mul_right hk hij
    omega
  have htel : ∑' n, (e n - e (n + 1)) = e 0 := by
    rw [he.tsum_sub ((summable_nat_add_iff 1).2 he), he.tsum_eq_zero_add]
    abel
  simpa [e, R, u, β, Δ, show ∀ n : ℕ, 2 * (n + 1) + 1 = 2 * n + 3 by omega] using htel

end MetaMathlibExt
