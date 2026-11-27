/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.GeneralizedFibonacciPolynomial
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecificLimits.Normed
import MathlibExt.NumberTheory.Recurrences.GeneralizedFibonacciIdentities

/-!
# Telescoping powers of gibonacci polynomial ratios

We prove the unconditional sum of successive differences of powered Fibonacci or Lucas
polynomial ratios along an arithmetic progression.
-/

namespace MetaMathlibExt

open Polynomial Asymptotics
open scoped Topology

namespace hasSum_gibonacciPoly_pow_ratio_telescoping

/-- In a two-root Binet sequence, the error in the powered ratio is geometrically summable. -/
private theorem summable_ratio_error {u : ℕ → ℝ} {a b c d : ℝ} (ha : a ≠ 0)
    (hc : c ≠ 0) (hq : |b / a| < 1) (hu : ∀ n, u n = c * a ^ n + d * b ^ n)
    (r m : ℕ) : Summable (fun n => (u (n + r) / u n) ^ m - a ^ (m * r)) := by
  let q := b / a
  let F (z : ℝ) := (a ^ r * (c + d * (z * q ^ r)) / (c + d * z)) ^ m
  have hfactor (n : ℕ) : u n = a ^ n * (c + d * q ^ n) := by
    rw [hu, show q = b / a from rfl, div_pow]
    field_simp
  have hratio (n : ℕ) : (u (n + r) / u n) ^ m = F (q ^ n) := by
    rw [hfactor (n + r), hfactor n, pow_add, pow_add, mul_assoc,
      mul_div_mul_left _ _ (pow_ne_zero n ha)]
  have hzero : F 0 = a ^ (m * r) := by
    rw [Nat.mul_comm m r, pow_mul]
    simp [F, hc]
  have hd : DifferentiableAt ℝ F 0 := by
    dsimp [F]
    fun_prop (disch := simp [hc])
  have hbound : (fun z => F z - F 0) =O[𝓝 0] (fun z => z) := by
    simpa using hd.isBigO_sub
  simp_rw [hratio, ← hzero]
  exact summable_of_isBigO_nat (summable_geometric_of_abs_lt_one hq)
    (hbound.comp_tendsto (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq))

end hasSum_gibonacciPoly_pow_ratio_telescoping

set_option linter.unusedVariables false in
/-- **A telescoping series of powers of gibonacci polynomial ratios.** Let $x > 0$ be real, let
$\alpha = (x + \sqrt{x^2 + 4})/2$, and let $g_n$ be either the Fibonacci polynomials $f_n(x)$,
given by $f_0 = 0$ and $f_1 = 1$, or the Lucas polynomials $l_n(x)$, given by $l_0 = 2$ and
$l_1 = x$, where both satisfy $z_{n+2} = x z_{n+1} + z_n$. Let $k$, $r$, $t$, $\lambda$ be positive
integers and $p$ a natural number with $t \le 2p$. Then the series
$$\sum_{n=1}^{\infty} \left[ \left( \frac{g_{(2pn+t-2p)k+r}}{g_{(2pn+t-2p)k}} \right)^{\lambda} -
\left( \frac{g_{(2pn+t)k+r}}{g_{(2pn+t)k}} \right)^{\lambda} \right]$$
converges unconditionally, and its sum is
$\left( g_{tk+r} / g_{tk} \right)^{\lambda} - \alpha^{\lambda r}$.

The source takes $x$ to be an integer; the statement is made for real $x > 0$, which contains the
positive integers.

Source: Thomas Koshy, *Sums Involving a Family of Gibonacci Polynomial Squares:
Generalizations*, The Fibonacci Quarterly 62 (2024), Article koshy11112023, Lemma 2.1
(`fq-2024-koshy11112023-lem-2.1`). -/
public theorem hasSum_gibonacciPoly_pow_ratio_telescoping (g : ℕ → ℤ[X])
    (hg : g = generalizedFibonacciPolynomial 0 1 X 1 ∨ g = generalizedFibonacciPolynomial 2 X X 1)
    {x : ℝ} (hx : 0 < x) {k p r t m : ℕ} (hk : 0 < k) (hr : 0 < r) (ht : 0 < t) (hm : 0 < m)
    (htp : t ≤ 2 * p) :
    HasSum (fun n : ℕ =>
        (aeval x (g ((2 * p * (n + 1) + t - 2 * p) * k + r)) /
            aeval x (g ((2 * p * (n + 1) + t - 2 * p) * k))) ^ m -
          (aeval x (g ((2 * p * (n + 1) + t) * k + r)) /
            aeval x (g ((2 * p * (n + 1) + t) * k))) ^ m)
      ((aeval x (g (t * k + r)) / aeval x (g (t * k))) ^ m -
        ((x + Real.sqrt (x ^ 2 + 4)) / 2) ^ (m * r)) := by
  let u (n : ℕ) := aeval x (g n)
  have hrec (n : ℕ) : u (n + 2) = x * u (n + 1) + u n := by
    rcases hg with rfl | rfl <;> simp [u]
  have hseeds : 0 ≤ u 0 ∧ 0 < u 1 := by
    rcases hg with rfl | rfl <;> norm_num [u, hx, map_ofNat]
  let Δ := Real.sqrt (x ^ 2 + 4)
  let α := (x + Δ) / 2
  let β := (x - Δ) / 2
  have hΔ : x < Δ := (Real.lt_sqrt hx.le).2 (by linarith)
  have hα : 0 < α := by dsimp [α]; linarith
  have hβ : β < 0 := by dsimp [β]; linarith
  have hq : |β / α| < 1 := by
    rw [abs_div, abs_of_neg hβ, abs_of_pos hα, div_lt_one hα]
    dsimp [α, β]
    linarith
  have hc : 0 < (u 1 - u 0 * β) / Δ := by
    apply div_pos _ (hx.trans hΔ)
    exact sub_pos.mpr ((mul_nonpos_of_nonneg_of_nonpos hseeds.1 hβ.le).trans_lt hseeds.2)
  let R (n : ℕ) := (u (n + r) / u n) ^ m
  have hsum : Summable (fun n => R n - α ^ (m * r)) :=
    hasSum_gibonacciPoly_pow_ratio_telescoping.summable_ratio_error
      hα.ne' hc.ne' hq (generalizedFibonacci_binet x u hrec) r m
  let index (n : ℕ) := (2 * p * n + t) * k
  let error (n : ℕ) := R (index n) - α ^ (m * r)
  have he : Summable error := by
    apply hsum.comp_injective (i := index)
    intro i j hij
    have hp : 0 < 2 * p := ht.trans_le htp
    exact Nat.eq_of_mul_eq_mul_left hp
      (Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_right hk hij))
  have htail : HasSum (fun n => error (n + 1)) ((∑' n, error n) - error 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 he.hasSum
  have htel : HasSum (fun n => R (index n) - R (index (n + 1))) (error 0) := by
    convert he.hasSum.sub htail using 1
    · funext n
      dsimp [error]
      ring
    · ring
  have hindex (n : ℕ) : 2 * p * (n + 1) + t - 2 * p = 2 * p * n + t := by
    rw [Nat.mul_succ]
    omega
  simpa [error, index, R, u, α, Δ, hindex] using htel

end MetaMathlibExt
