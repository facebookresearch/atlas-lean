/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import MathlibExt.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal

/-!
# The inverse central binomial series for the square of arcsine

For real `x` with `|x| < 1`, termwise differentiation reduces the series for
`(arcsin x) ^ 2 / 2` to Lehmer's reciprocal central binomial series.

## References

* D. H. Lehmer, *Interesting Series Involving the Central Binomial Coefficient*,
  The American Mathematical Monthly **92** (1985), pp. 449–457, equation (13).
* The integration argument was adapted from `e22A_eq_arcsin_sq` and its supporting lemmas in
  `MathlibExt.Analysis.Ramanujan.Part1Ch9Entry22Chudnovsky`.
-/

open Set

namespace MetaMathlibExt

private noncomputable def squareTerm (n : ℕ) (x : ℝ) : ℝ :=
  ((4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)) * x ^ (2 * n + 2)

private noncomputable def derivTerm (n : ℕ) (x : ℝ) : ℝ :=
  (2 * (4 : ℝ) ^ n / (((n : ℝ) + 1) * (n + 1).centralBinom)) * x ^ (2 * n + 1)

private lemma hasDerivAt_squareTerm (n : ℕ) (x : ℝ) :
    HasDerivAt (squareTerm n) (derivTerm n x) x := by
  unfold squareTerm
  refine ((hasDerivAt_pow (2 * n + 2) x).const_mul _).congr_deriv ?_
  rw [derivTerm, show 2 * n + 2 - 1 = 2 * n + 1 by omega]
  push_cast
  field_simp

private lemma hasSum_derivTerm {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => derivTerm n x) (Real.arcsin x / Real.sqrt (1 - x ^ 2)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [derivTerm, zero_pow (Nat.succ_ne_zero _)]
  have h := (arcsin_central_binomial_reciprocal_series x hx).div_const (2 * x)
  convert h using 1
  · funext n
    have hxpow : (2 * x) ^ (2 * (n + 1)) = (4 : ℝ) ^ n * 4 * (x ^ (2 * n + 1) * x) := by
      rw [mul_pow, pow_mul (2 : ℝ), show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ (4 : ℝ),
        show 2 * (n + 1) = (2 * n + 1) + 1 by omega, pow_succ x]
    have hb : ((n + 1).centralBinom : ℝ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero (n + 1)
    rw [derivTerm, hxpow, ← Nat.centralBinom_eq_two_mul_choose]
    push_cast
    field_simp
    ring
  · rw [div_mul_eq_mul_div, mul_div_assoc (2 * x),
      mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero hx0)]

private lemma squareSeries_local {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    Summable (fun n => squareTerm n x) ∧
      HasDerivAt (fun y => ∑' n, squareTerm n y) (Real.arcsin x / Real.sqrt (1 - x ^ 2)) x := by
  obtain ⟨r, hxr, hr1⟩ := exists_between (abs_lt.mpr hx)
  have hr0 : 0 < r := (abs_nonneg x).trans_lt hxr
  have hr : |r| < 1 := by simpa only [abs_of_pos hr0] using hr1
  have hu := (hasSum_derivTerm hr).summable
  have hsum0 : Summable (fun n => squareTerm n 0) := by simp [squareTerm]
  have h0 : (0 : ℝ) ∈ Ioo (-r) r := by simp [hr0]
  have hdiff (n : ℕ) (y : ℝ) (_ : y ∈ Ioo (-r) r) := hasDerivAt_squareTerm n y
  have hbound (n : ℕ) (y : ℝ) (hy : y ∈ Ioo (-r) r) :
      ‖derivTerm n y‖ ≤ derivTerm n r := by
    unfold derivTerm
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) (abs_lt.mpr hy).le _)
      (by positivity)
  have hmem : x ∈ Ioo (-r) r := abs_lt.mp hxr
  refine ⟨summable_of_summable_hasDerivAt_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hdiff hbound h0 hsum0 hmem, ?_⟩
  rw [← (hasSum_derivTerm (abs_lt.mpr hx)).tsum_eq]
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    hdiff hbound h0 hsum0 hmem

/-- **Lehmer’s inverse central binomial series for the square of arcsine.** For a real number
For a real number $x$ with $|x| < 1$, the series converges unconditionally and satisfies
$$
\sum_{n=0}^{\infty}\frac{4^n x^{2n+2}}{\binom{2(n+1)}{n+1}(n+1)^2}
= \frac{(\arcsin x)^2}{2}.
$$ -/
public theorem hasSum_arcsin_sq_div_two {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n : ℕ =>
      ((4 : ℝ) ^ n / (((n + 1).centralBinom : ℝ) * ((n : ℝ) + 1) ^ 2)) * x ^ (2 * n + 2))
      (Real.arcsin x ^ 2 / 2) := by
  have hd (y : ℝ) (hy : y ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (fun z => Real.arcsin z ^ 2 / 2) (Real.arcsin y / Real.sqrt (1 - y ^ 2)) y := by
    refine (((Real.hasDerivAt_arcsin hy.1.ne' hy.2.ne).pow 2).div_const 2).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    ring
  have heq :
      EqOn (fun y => ∑' n, squareTerm n y) (fun y => Real.arcsin y ^ 2 / 2) (Ioo (-1 : ℝ) 1) := by
    refine isOpen_Ioo.eqOn_of_deriv_eq isPreconnected_Ioo
      (fun y hy => (squareSeries_local hy).2.differentiableAt.differentiableWithinAt)
      (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
      (fun y hy => (squareSeries_local hy).2.deriv.trans (hd y hy).deriv.symm)
      (x := 0) (by norm_num) ?_
    simp [squareTerm]
  change HasSum (fun n => squareTerm n x) (Real.arcsin x ^ 2 / 2)
  have hvalue : (∑' n, squareTerm n x) = Real.arcsin x ^ 2 / 2 := heq (abs_lt.mp hx)
  rw [← hvalue]
  exact (squareSeries_local (abs_lt.mp hx)).1.hasSum

end MetaMathlibExt
