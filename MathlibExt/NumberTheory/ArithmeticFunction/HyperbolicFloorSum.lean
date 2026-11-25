/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Log-weighted difference series in hyperbolic floor sums

The mean value theorem bounds the unit difference of `(log x)^i / x` by a power
`x^(ε - 2)` for arbitrarily small positive `ε`. This gives a summable majorant
after multiplication by an arithmetic function of sublinear power growth.
-/

open Asymptotics Filter

namespace MetaMathlibExt

private theorem isBigO_log_pow_div_sub (i : ℕ) {ε : ℝ} (hε : 0 < ε) (hε₂ : ε ≤ 2) :
    (fun x : ℝ => Real.log x ^ i / x - Real.log (x + 1) ^ i / (x + 1)) =O[atTop]
      fun x : ℝ => x ^ (ε - 2) := by
  let g (x : ℝ) := Real.log x ^ i / x
  let p (x : ℝ) := i * Real.log x ^ (i - 1) - Real.log x ^ i
  have hg (x : ℝ) (hx : 0 < x) : HasDerivAt g (p x / x ^ 2) x := by
    simpa [g, p, mul_assoc, hx.ne'] using
      (((Real.hasDerivAt_log hx.ne').fun_pow i).fun_div (hasDerivAt_id x) hx.ne')
  have hlog (k : ℕ) : (fun x : ℝ => Real.log x ^ k) =o[atTop] fun x : ℝ => x ^ ε := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (k : ℝ) hε
  have hp : p =o[atTop] fun x : ℝ => x ^ ε :=
    ((hlog (i - 1)).const_mul_left (i : ℝ)).sub (hlog i)
  obtain ⟨a, ha⟩ := eventually_atTop.1 (hp.bound zero_lt_one)
  apply IsBigO.of_bound'
  filter_upwards [eventually_ge_atTop a, eventually_gt_atTop 0] with x hxa hx
  obtain ⟨y, hy, hslope⟩ := exists_hasDerivAt_eq_slope g (fun t => p t / t ^ 2)
    (show x < x + 1 by linarith)
    (fun t ht => (hg t (hx.trans_le ht.1)).continuousAt.continuousWithinAt)
    (fun t ht => hg t (hx.trans ht.1))
  have hypos := hx.trans hy.1
  have hpy : ‖p y‖ ≤ y ^ ε := by
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg hypos.le ε)] using ha y (hxa.trans hy.1.le)
  calc
    ‖g x - g (x + 1)‖ = ‖p y / y ^ 2‖ := by
      rw [norm_sub_rev, hslope]
      simp
    _ ≤ y ^ ε / y ^ 2 := by
      rw [norm_div, Real.norm_of_nonneg (sq_nonneg y)]
      gcongr
    _ = y ^ (ε - 2) := (Real.rpow_sub_natCast hypos.ne' ε 2).symm
    _ ≤ x ^ (ε - 2) := Real.rpow_le_rpow_of_nonpos hx hy.1.le (sub_nonpos.mpr hε₂)
    _ = ‖x ^ (ε - 2)‖ := (Real.norm_of_nonneg (Real.rpow_nonneg hx.le _)).symm

/-- **Absolute convergence of a log-weighted difference series.** Let $f$ be a real function on
the natural numbers with $f(n) = O(n^\alpha)$ as $n \to \infty$ for some real $\alpha$ with
$0 \le \alpha < 1$. Then for every natural number $i$ the series
$$\sum_{n \ge 1} f(n) \left( \frac{(\log n)^i}{n} - \frac{(\log (n+1))^i}{n+1} \right)$$
converges absolutely.

Source: Meselem Karras and Mihoub Bouderbala, *Hyperbolic Summation Involving Certain
Arithmetic Functions and the Integer Part Function*, INTEGERS 26 (2026), Article A37,
Lemma 1 (`integers-2026-A37-lem-1`). -/
public theorem summable_abs_mul_log_pow_div_sub
    (f : ℕ → ℝ) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hf : (fun n : ℕ => f n) =O[atTop] fun n : ℕ => (n : ℝ) ^ α) (i : ℕ) :
    Summable fun n : ℕ =>
      |f (n + 1) * (Real.log (n + 1) ^ i / (n + 1) - Real.log (n + 2) ^ i / (n + 2))| := by
  obtain ⟨ε, hε, hεα⟩ := exists_between (sub_pos.mpr hα1)
  have hd := (isBigO_log_pow_div_sub i hε (by linarith)).comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hs : Summable (fun n : ℕ => f n *
      (Real.log n ^ i / n - Real.log (n + 1) ^ i / (n + 1))) := by
    apply summable_of_isBigO_nat (Real.summable_nat_rpow.mpr
      (show α + (ε - 2) < -1 by linarith))
    refine (hf.mul hd).congr' .rfl ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (Real.rpow_add (by exact_mod_cast hn : 0 < (n : ℝ)) _ _).symm
  simpa only [Nat.cast_add_one, add_assoc, one_add_one_eq_two] using
    (summable_nat_add_iff 1).mpr hs.abs

end MetaMathlibExt
