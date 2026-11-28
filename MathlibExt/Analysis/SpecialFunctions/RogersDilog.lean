/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Dilog
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Rogers dilogarithm

`Real.rogersDilog` is the real dilogarithm plus the half-logarithm product. On `[0, 1]`
it is the continuous Rogers dilogarithm, with the endpoint convention `Real.log 0 = 0`.
Reflection holds on `[0, 1]`, and Abel's five-term relation holds when both arguments
lie in `(0, 1)`.

## References

* Chance Sanford, *A Dilogarithm Series and a Generalization of a Theorem of Bridgeman*,
  INTEGERS 25 (2025), Article A52, pp. 1–15, equations (1) and (2).
* The analytic proofs are extracted from the proof of
  `MetaMathlibExt.rogersDilog_sanford_symmetric_series` in
  `MathlibExt.NumberTheory.SanfordSymmetricSeries`.
-/

open Set

namespace Real

/-- The Rogers dilogarithm on `[0, 1]`, given by `Li₂(x) + log x * log (1 - x) / 2`.
Lean's `log 0 = 0` gives the usual endpoint values. The formula is totalized; no
analytic continuation is intended. -/
public noncomputable def rogersDilog (x : ℝ) : ℝ :=
  li2PowerSeries x + log x * log (1 - x) / 2

/-- For real $x$, the totalized formula for the Rogers dilogarithm is

$$
L(x) = \sum_{n=0}^{\infty} \frac{x^{n+1}}{(n+1)^2} + \frac{1}{2}\log x\,\log(1-x).
$$

The series term is `0` when the series is not summable; the logarithmic term is still included.
On $[0, 1]$ this agrees with the usual Rogers dilogarithm, using Lean's $\log 0 = 0$
at the endpoints. -/
public theorem rogersDilog_eq_tsum_add_log_mul_log (x : ℝ) :
    rogersDilog x = (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) +
      log x * log (1 - x) / 2 := by
  rw [rogersDilog, li2PowerSeries_eq_tsum]

/-- The Rogers dilogarithm is nonnegative on `(0, 1)`. -/
public theorem rogersDilog_nonneg {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : 0 ≤ rogersDilog x := by
  rw [rogersDilog_eq_tsum_add_log_mul_log]
  exact add_nonneg (tsum_nonneg fun n => div_nonneg (pow_nonneg hx.1.le _) (sq_nonneg _))
    (div_nonneg (mul_nonneg_of_nonpos_of_nonpos (log_nonpos hx.1.le hx.2.le)
      (log_nonpos (sub_nonneg.mpr hx.2.le) (sub_le_self _ hx.1.le))) (by norm_num))

/-- The Rogers dilogarithm vanishes at `0`. -/
@[simp]
public theorem rogersDilog_zero : rogersDilog 0 = 0 := by simp [rogersDilog, li2PowerSeries_zero]

/-- For $0 \le x \le 1$, the Rogers dilogarithm satisfies $L(x) + L(1-x) = \pi^2/6$. -/
public theorem rogersDilog_reflection {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    rogersDilog x + rogersDilog (1 - x) = π ^ 2 / 6 := by
  rcases hx.1.eq_or_lt with rfl | hx₀
  · simp [rogersDilog, li2PowerSeries_zero, li2PowerSeries_one]
  rcases hx.2.eq_or_lt with rfl | hx₁
  · simp [rogersDilog, li2PowerSeries_zero, li2PowerSeries_one]
  simp only [rogersDilog, sub_sub_cancel]
  linarith [li2PowerSeries_reflection ⟨hx₀, hx₁⟩]

/-- The Rogers dilogarithm is continuous on `[0, 1]`, including both endpoints. -/
public theorem continuousOn_rogersDilog : ContinuousOn rogersDilog (Icc 0 1) := by
  -- Reflection expresses the function in terms of two power series continuous at the endpoints.
  have h₁ := continuousOn_li2PowerSeries.mono (show Icc (0 : ℝ) 1 ⊆ Icc (-1) 1 by
    intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
  have h₂ : ContinuousOn (fun x => li2PowerSeries (1 - x)) (Icc (0 : ℝ) 1) :=
    h₁.comp (continuousOn_const.sub continuousOn_id)
      (fun x hx => ⟨sub_nonneg.mpr hx.2, sub_le_self 1 hx.1⟩)
  apply (((h₁.sub h₂).add (continuousOn_const (c := π ^ 2 / 6))).div_const 2).congr
  intro x hx
  have he := rogersDilog_reflection hx
  simp only [rogersDilog, sub_sub_cancel, Pi.add_apply, Pi.sub_apply] at he ⊢
  linarith

private lemma hasDerivAt_rogersDilog {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt rogersDilog (-(log (1 - x) / x + log x / (1 - x)) / 2) x := by
  have hd := hasDerivAt_li2PowerSeries (by simpa only [abs_of_pos hx.1] using hx.2) hx.1.ne'
  have hlog := ((hasDerivAt_id' x).const_sub 1).log (sub_pos.mpr hx.2).ne'
  refine (hd.add (((hasDerivAt_log hx.1.ne').mul hlog).div_const 2)).congr_deriv ?_
  ring

-- The two new arguments of Abel's relation are step x y and step y x.
private noncomputable def step (x y : ℝ) : ℝ := x * (1 - y) / (1 - x * y)

private lemma one_sub_step {x y : ℝ} (hd : 1 - x * y ≠ 0) :
    1 - step x y = (1 - x) / (1 - x * y) := by
  unfold step
  field_simp
  ring

private lemma mul_mem {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    x * y ∈ Ioo (0 : ℝ) 1 := by
  simpa only [Ioo.coe_mul] using (((⟨x, hx⟩ : Ioo (0 : ℝ) 1) * ⟨y, hy⟩).2)

/-- If $0 < x, y < 1$, the argument $x(1-y)/(1-xy)$ of Abel's five-term relation
also lies in $(0, 1)$. -/
public theorem abel_five_term_arg_mem_Ioo {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hy : y ∈ Ioo (0 : ℝ) 1) : x * (1 - y) / (1 - x * y) ∈ Ioo (0 : ℝ) 1 := by
  change step x y ∈ Ioo (0 : ℝ) 1
  have hd := sub_pos.mpr (mul_mem hx hy).2
  refine ⟨div_pos (mul_pos hx.1 (sub_pos.mpr hy.2)) hd, sub_pos.mp ?_⟩
  rw [one_sub_step hd.ne']
  exact div_pos (sub_pos.mpr hx.2) hd

-- Vary x with y fixed. After expanding the four logarithms of the two new
-- arguments and their complements, the derivative of the five-term difference vanishes.
private lemma fiveTerm_deriv {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun z => rogersDilog z - rogersDilog (z * y) -
      rogersDilog (step z y) - rogersDilog (step y z)) 0 x := by
  have hxy := mul_mem hx hy
  have hd := (sub_pos.mpr hxy.2).ne'
  have hdx := (sub_pos.mpr hx.2).ne'
  have hdy := (sub_pos.mpr hy.2).ne'
  have hprod := (hasDerivAt_id' x).mul_const y
  have hden := hprod.const_sub 1
  have hu := ((hasDerivAt_id' x).mul_const (1 - y)).div hden hd
  have hv := (((hasDerivAt_id' x).const_sub 1).const_mul y).div
    (((hasDerivAt_id' x).const_mul y).const_sub 1) (by simpa only [mul_comm y x] using hd)
  have hu_mem : step x y ∈ Ioo (0 : ℝ) 1 := abel_five_term_arg_mem_Ioo hx hy
  have hv_mem : step y x ∈ Ioo (0 : ℝ) 1 := abel_five_term_arg_mem_Ioo hy hx
  refine ((((hasDerivAt_rogersDilog hx).sub ((hasDerivAt_rogersDilog hxy).comp x hprod)).sub
    ((hasDerivAt_rogersDilog hu_mem).comp x hu)).sub
      ((hasDerivAt_rogersDilog hv_mem).comp x hv)).congr_deriv ?_
  rw [one_sub_step hd, one_sub_step (by rwa [mul_comm y x]), step, step, mul_comm y x]
  rw [log_div hdx hd, log_div hdy hd, log_div (mul_ne_zero hx.1.ne' hdy) hd,
    log_div (mul_ne_zero hy.1.ne' hdx) hd, log_mul hx.1.ne' hy.1.ne',
    log_mul hx.1.ne' hdy, log_mul hy.1.ne' hdx]
  field_simp [hx.1.ne', hy.1.ne', hdx, hdy, hd]
  ring

/-- Abel's five-term relation for the Rogers dilogarithm $L$: for $0 < x, y < 1$,

$$
L(x) + L(y) = L(xy) + L\left(\frac{x(1-y)}{1-xy}\right)
  + L\left(\frac{y(1-x)}{1-yx}\right).
$$
-/
public theorem rogersDilog_five_term {x y : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    rogersDilog x + rogersDilog y = rogersDilog (x * y) +
      rogersDilog (x * (1 - y) / (1 - x * y)) + rogersDilog (y * (1 - x) / (1 - y * x)) := by
  change rogersDilog x + rogersDilog y =
    rogersDilog (x * y) + rogersDilog (step x y) + rogersDilog (step y x)
  let F (z : ℝ) := rogersDilog z - rogersDilog (z * y) -
    rogersDilog (step z y) - rogersDilog (step y z)
  have compL {f : ℝ → ℝ} (hc : ContinuousOn f (Icc 0 x)) (h₀ : f 0 ∈ Icc 0 1)
      (hi : ∀ z ∈ Ioo (0 : ℝ) 1, f z ∈ Ioo 0 1) :
      ContinuousOn (fun z => rogersDilog (f z)) (Icc 0 x) := by
    apply continuousOn_rogersDilog.comp hc
    intro z hz
    rcases hz.1.eq_or_lt with rfl | h
    · exact h₀
    · exact Ioo_subset_Icc_self (hi z ⟨h, hz.2.trans_lt hx.2⟩)
  have hd (z : ℝ) (hz : z ∈ Icc 0 x) : 1 - z * y ≠ 0 :=
    (sub_pos.mpr ((mul_le_mul_of_nonneg_right hz.2 hy.1.le).trans_lt (mul_mem hx hy).2)).ne'
  have hu : ContinuousOn (fun z => step z y) (Icc 0 x) :=
    (continuousOn_id.mul continuousOn_const).div
      (continuousOn_const.sub (continuousOn_id.mul continuousOn_const)) hd
  have hv : ContinuousOn (step y) (Icc 0 x) :=
    (continuousOn_const.mul (continuousOn_const.sub continuousOn_id)).div
      (continuousOn_const.sub (continuousOn_const.mul continuousOn_id))
      (fun z hz => by simpa only [mul_comm y z] using hd z hz)
  have hc : ContinuousOn F (Icc 0 x) :=
    (((continuousOn_rogersDilog.mono (Icc_subset_Icc_right hx.2.le)).sub
      (compL (continuousOn_id.mul continuousOn_const) (by simp) (fun _ hz => mul_mem hz hy))).sub
      (compL hu (by simp [step]) (fun _ hz => abel_five_term_arg_mem_Ioo hz hy))).sub
      (compL hv (by simpa [step] using Ioo_subset_Icc_self hy)
        (fun _ hz => abel_five_term_arg_mem_Ioo hy hz))
  obtain ⟨c, hc', he⟩ := exists_hasDerivAt_eq_slope F (fun _ => 0) hx.1 hc
    (fun z hz => fiveTerm_deriv ⟨hz.1, hz.2.trans hx.2⟩ hy)
  have heq := (div_eq_zero_iff.mp he.symm).resolve_right (by simpa using hx.1.ne')
  simp only [F, step, zero_mul, mul_zero, sub_zero, mul_one,
    div_one, rogersDilog_zero] at heq ⊢
  linarith

end Real
