/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# x^2 sin(1/x^2): derivative exists but is not integrable

The following OpenBMB notice applies to the adapted statement and its documentation.

Copyright (c) 2026 OpenBMB

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

Attribution and modification notice: the statement below is taken from openbmb/ma-proofbench at
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_99.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_99 … := by sorry` into the Batteries `theorem_wanted`
`differentiable_and_not_integrableOn_deriv_sq_mul_sin_inv_sq`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.XSqSinInvSqNonintegrableDerivWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # An everywhere differentiable function with nonintegrable derivative

The slopes at zero are bounded by `|x|`. Nonintegrability follows because the differences of
successive values with alternating sine factors dominate a harmonic sequence; the fundamental
theorem of calculus would bound the sum of the differences by the integral of the absolute
value of the derivative.
-/

@[expose] public section

namespace MathlibExt.Analysis.Calculus.XSqSinInvSqNonintegrableDerivWanted

open MeasureTheory Filter Set
open scoped Topology

private noncomputable def f (x : ℝ) : ℝ := x ^ 2 * Real.sin (1 / x ^ 2)

private theorem f_diff (x : ℝ) : DifferentiableAt ℝ f x := by
  by_cases hx : x = 0
  · subst x
    apply HasDerivAt.differentiableAt (f' := 0)
    rw [hasDerivAt_iff_tendsto_slope, tendsto_zero_iff_norm_tendsto_zero]
    have hbound (y : ℝ) : ‖slope f 0 y‖ ≤ ‖y‖ := by
      by_cases hy : y = 0
      · simp [hy]
      have heq : slope f 0 y = y * Real.sin (1 / y ^ 2) := by
        rw [slope_def_field]
        simp only [f, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, sub_zero]
        field_simp
      rw [heq, norm_mul, Real.norm_eq_abs (Real.sin _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
    have hlim : Tendsto (fun y : ℝ => ‖y‖) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [norm_zero] using ((continuous_norm.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => norm_nonneg _) hbound
  · have hp : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) x := differentiableAt_id.pow 2
    have hd : DifferentiableAt ℝ (fun y : ℝ => 1 / y ^ 2) x :=
      (differentiableAt_const (1 : ℝ)).div hp (pow_ne_zero 2 hx)
    exact hp.mul hd.sin

private noncomputable def phase (n : ℕ) : ℝ := Real.pi / 2 + n * Real.pi

private theorem phase_pos (n : ℕ) : 0 < phase n := by
  unfold phase
  positivity

private noncomputable def a (n : ℕ) : ℝ := 1 / Real.sqrt (phase n)

private theorem a_pos (n : ℕ) : 0 < a n :=
  one_div_pos.mpr (Real.sqrt_pos.2 (phase_pos n))

private theorem a_lt_one (n : ℕ) : a n < 1 := by
  have hp : 1 < phase n := by
    unfold phase
    have hn : 0 ≤ (n : ℝ) * Real.pi := by positivity
    linarith [Real.pi_gt_three]
  have hs : 1 < Real.sqrt (phase n) := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hp
  exact (div_lt_iff₀ (lt_trans zero_lt_one hs)).2 (by simpa only [one_mul] using hs)

private theorem a_succ_le (n : ℕ) : a (n + 1) ≤ a n := by
  have hp : phase n < phase (n + 1) := by
    unfold phase
    push_cast
    linarith [Real.pi_pos]
  exact (one_div_lt_one_div_of_lt (Real.sqrt_pos.2 (phase_pos n))
    (Real.sqrt_lt_sqrt (phase_pos n).le hp)).le

private theorem f_a (n : ℕ) : f (a n) = (1 / phase n) * (-1) ^ n := by
  have hsq : a n ^ 2 = 1 / phase n := by
    rw [a, div_pow, one_pow, Real.sq_sqrt (phase_pos n).le]
  rw [f, hsq]
  simp only [one_div, inv_inv, phase, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]

private theorem harmonic_le_diff (n : ℕ) :
    1 / (Real.pi * (n + 1 : ℝ)) ≤ ‖f (a n) - f (a (n + 1))‖ := by
  have heq : f (a n) - f (a (n + 1)) = (-1) ^ n * (1 / phase n + 1 / phase (n + 1)) := by
    rw [f_a n, f_a (n + 1), pow_succ]
    ring
  have hn : 0 ≤ 1 / phase n := one_div_nonneg.mpr (phase_pos n).le
  have hsucc : 0 ≤ 1 / phase (n + 1) := one_div_nonneg.mpr (phase_pos (n + 1)).le
  rw [Real.norm_eq_abs, heq, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (add_nonneg hn hsucc)]
  have hphase : phase n ≤ Real.pi * (n + 1 : ℝ) := by
    unfold phase
    nlinarith [Real.pi_pos]
  exact (div_le_div_of_nonneg_left zero_le_one (phase_pos n) hphase).trans
    (le_add_of_nonneg_right hsucc)

private theorem not_integrable_f_deriv : ¬ IntegrableOn (deriv f) (Icc (-1 : ℝ) 1) := by
  intro hf
  let g (x : ℝ) := ‖deriv f x‖
  have hg : IntegrableOn g (Icc (-1 : ℝ) 1) := hf.norm
  have ha (n : ℕ) : a n ∈ Icc (-1 : ℝ) 1 :=
    ⟨(by linarith [a_pos n]), (a_lt_one n).le⟩
  have hsub (i j : ℕ) : uIcc (a i) (a j) ⊆ Icc (-1 : ℝ) 1 :=
    uIcc_subset_Icc (ha i) (ha j)
  have int_f (i j : ℕ) : IntervalIntegrable (deriv f) volume (a i) (a j) :=
    (hf.mono_set (hsub i j)).intervalIntegrable
  have int_g (i j : ℕ) : IntervalIntegrable g volume (a i) (a j) :=
    (hg.mono_set (hsub i j)).intervalIntegrable
  have hbound (n : ℕ) : ‖f (a n) - f (a (n + 1))‖ ≤ ∫ x in a (n + 1)..a n, g x := by
    rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => (f_diff x).hasDerivAt) (int_f (n + 1) n)]
    exact intervalIntegral.norm_integral_le_integral_norm (a_succ_le n)
  have htel (n : ℕ) : (∑ i ∈ Finset.range n, ∫ x in a (i + 1)..a i, g x) =
      ∫ x in a n..a 0, g x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih, add_comm,
        intervalIntegral.integral_add_adjacent_intervals (int_g (n + 1) n) (int_g n 0)]
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, 1 / (Real.pi * (i + 1 : ℝ))) ≤
      ∫ x in Icc (-1 : ℝ) 1, g x := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, ∫ x in a (i + 1)..a i, g x :=
        Finset.sum_le_sum fun i _ => (harmonic_le_diff i).trans (hbound i)
      _ = ∫ x in a n..a 0, g x := htel n
      _ ≤ ∫ x in Icc (-1 : ℝ) 1, g x := by
        have han : a n ≤ a 0 := (antitone_nat_of_succ_le a_succ_le) (Nat.zero_le n)
        rw [intervalIntegral.integral_of_le han]
        apply setIntegral_mono_set hg (Eventually.of_forall fun _ => norm_nonneg _)
        exact Eventually.of_forall fun x hx => ⟨(ha n).1.trans hx.1.le, hx.2.trans (ha 0).2⟩
  have hs := summable_of_sum_range_le (fun n : ℕ => by positivity :
    ∀ n : ℕ, 0 ≤ 1 / (Real.pi * (n + 1 : ℝ))) hsum
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff 1).mp
  refine (hs.mul_left Real.pi).congr fun n => ?_
  push_cast
  field_simp [Real.pi_ne_zero]
/-- **The derivative of $x^2 \sin(1/x^2)$ exists everywhere but is not integrable.** Let
$F : \mathbb{R} \to \mathbb{R}$ be given by $F(x) = x^2 \sin(1/x^2)$ for $x \ne 0$ and $F(0) = 0$.
Then $F$ is differentiable at every real $x$, but its derivative $F'$ is not Lebesgue integrable
on $[-1,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_99.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem differentiable_and_not_integrableOn_deriv_sq_mul_sin_inv_sq
    (F : ℝ → ℝ) (h0 : F 0 = 0)
    (hF : ∀ x ≠ 0, F x = x ^ 2 * Real.sin (1 / (x ^ 2))) :
    (∀ x : ℝ, DifferentiableAt ℝ F x) ∧
      ¬ MeasureTheory.IntegrableOn (fun x : ℝ => deriv F x) (Set.Icc (-1 : ℝ) (1 : ℝ)) := by
  have heq : F = f := by
    funext x
    by_cases hx : x = 0
    · simpa [hx, f] using h0
    · exact hF x hx
  rw [heq]
  exact ⟨f_diff, not_integrable_f_deriv⟩

end MathlibExt.Analysis.Calculus.XSqSinInvSqNonintegrableDerivWanted
