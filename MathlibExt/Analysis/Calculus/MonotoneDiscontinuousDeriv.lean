/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement of `exists_monotone_differentiable_not_continuous_deriv`
below is used under the following license.

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
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.

Attribution and modification notice: the statement below is taken from
openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level1/ma_proofbench_l1_92.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation
of LLMs for Theorem Proving in Mathematical Analysis*,
arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above.
Changes made: converted the original theorem statement into a completed
existential theorem, moved the informal problem statement docstring onto
it, and placed the construction and supporting declarations in the
namespace `MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv`.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Monotonically differentiable function with discontinuous derivative

We construct a monotone function on `ℝ` that is differentiable everywhere
but whose derivative is not continuous.

The construction is

  f(x) = 0                                      if x = 0,
  f(x) = 3x + (x² / (1 + x²)) sin(1/x)          otherwise.

We prove that the function is differentiable at every point, that its
derivative is nonnegative, and thus the function is monotone.

Finally, we show that the derivative is discontinuous at zero by
considering a sequence approaching zero along which the oscillatory
trigonometric terms have fixed values.
-/

@[expose] public section

noncomputable section

namespace MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv

/-- The explicit function used in the construction. -/
private def monotoneDiscontinuousDerivFn (x : ℝ) : ℝ :=
  if x = 0 then 0
  else
    3 * x +
      (x ^ 2 / (1 + x ^ 2)) * Real.sin (1 / x)
/-- Away from zero, the function has its explicit nonzero formula. -/
private lemma apply_eq (x : ℝ) (hx : x ≠ 0) :
    monotoneDiscontinuousDerivFn x =
      3 * x +
        (x ^ 2 / (1 + x ^ 2)) * Real.sin (1 / x) := by
  simp [monotoneDiscontinuousDerivFn, hx]
/-- The derivative formula away from zero. -/
private def derivativeFormula (x : ℝ) : ℝ :=
  3 +
    (2 * x / (1 + x ^ 2) ^ 2) * Real.sin (1 / x) -
    (1 / (1 + x ^ 2)) * Real.cos (1 / x)
/-- The function has derivative `3` at zero. -/
private theorem hasDerivAt_zero :
    HasDerivAt monotoneDiscontinuousDerivFn 3 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  unfold slope
  simp only [smul_eq_mul, vsub_eq_sub, monotoneDiscontinuousDerivFn]
  have hmain :
      Filter.Tendsto
        (fun b : ℝ =>
          3 + b / (1 + b ^ 2) * Real.sin (1 / b))
        (nhdsWithin 0 {0}ᶜ) (nhds 3) := by
    have hsmall :
        Filter.Tendsto
          (fun b : ℝ =>
            b / (1 + b ^ 2) * Real.sin (1 / b))
          (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have hid :
          Filter.Tendsto (fun b : ℝ => b)
            (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        exact Filter.tendsto_id.mono_left nhdsWithin_le_nhds
      have habs :
          Filter.Tendsto (fun b : ℝ => |b|)
            (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
        simpa only [Function.comp_def, id_eq, abs_zero] using
          (continuous_abs.continuousAt.tendsto.comp hid)
      have hnonneg :
          ∀ᶠ b : ℝ in nhdsWithin 0 {0}ᶜ,
            0 ≤ |b / (1 + b ^ 2) * Real.sin (1 / b)| := by
        filter_upwards with b
        exact abs_nonneg _
      have hbound :
          ∀ᶠ b : ℝ in nhdsWithin 0 {0}ᶜ,
            |b / (1 + b ^ 2) * Real.sin (1 / b)| ≤ |b| := by
        filter_upwards with b
        have hd : 1 ≤ |1 + b ^ 2| := by
          rw [abs_of_pos (by positivity)]
          nlinarith [sq_nonneg b]
        have hs := Real.abs_sin_le_one (1 / b)
        rw [abs_mul, abs_div]
        calc
          |b| / |1 + b ^ 2| * |Real.sin (1 / b)|
              ≤ |b| / |1 + b ^ 2| * 1 :=
            mul_le_mul_of_nonneg_left hs (by positivity)
          _ = |b| / |1 + b ^ 2| := by ring
          _ ≤ |b| := by
            exact div_le_self (abs_nonneg b) hd
      have habs_small := squeeze_zero' hnonneg hbound habs
      exact tendsto_zero_iff_norm_tendsto_zero.mpr habs_small
    simpa using tendsto_const_nhds.add hsmall
  apply (Filter.tendsto_congr' ?_).2 hmain
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  simp [hx0]
  field_simp
/-- Away from zero, the function has the derivative given by
`derivativeFormula`. -/
private theorem hasDerivAt_ne_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt monotoneDiscontinuousDerivFn
      (derivativeFormula x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1
    · funext y
      rfl
    · norm_num
  have hden : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x 1).add hpow using 1
    · ring
  have hfrac :
      HasDerivAt (fun y : ℝ => y ^ 2 / (1 + y ^ 2))
        (2 * x / (1 + x ^ 2) ^ 2) x := by
    convert hpow.div hden
      (by positivity : 1 + x ^ 2 ≠ 0) using 1
    · field_simp
      ; ring
  have hinv :
      HasDerivAt (fun y : ℝ => 1 / y) (-(x ^ 2)⁻¹) x := by
    convert (hasDerivAt_inv hx) using 1 ; norm_num
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (1 / y))
        (Real.cos (1 / x) * (-(x ^ 2)⁻¹)) x := by
    exact (Real.hasDerivAt_sin (1 / x)).comp x hinv
  have hprod := hfrac.mul hsin
  have hlinear : HasDerivAt (fun y : ℝ => 3 * y) 3 x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul 3
  have hexplicit :
      HasDerivAt
        (fun y : ℝ =>
          3 * y + (y ^ 2 / (1 + y ^ 2)) * Real.sin (1 / y))
        (derivativeFormula x) x := by
    convert hlinear.add hprod using 1
    · unfold derivativeFormula
      field_simp [pow_ne_zero 2 hx,
        ne_of_gt (show 0 < 1 + x ^ 2 by positivity)]
      ; ring
  apply hexplicit.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact apply_eq y hy
/-- The derivative at zero is `3`. -/
private theorem deriv_zero :
    deriv monotoneDiscontinuousDerivFn 0 = 3 := by
  exact hasDerivAt_zero.deriv
/-- Away from zero, the derivative is given by the explicit formula. -/
private theorem deriv_ne_zero (x : ℝ) (hx : x ≠ 0) :
    deriv monotoneDiscontinuousDerivFn x =
      derivativeFormula x := by
  exact (hasDerivAt_ne_zero x hx).deriv
/-- The derivative formula is bounded below by `1`. -/
private theorem derivativeFormula_ge_one (x : ℝ) :
    1 ≤ derivativeFormula x := by
  unfold derivativeFormula
  have hs : |Real.sin (1 / x)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hc : Real.cos (1 / x) ≤ 1 :=
    Real.cos_le_one _
  have hd : 0 < 1 + x ^ 2 := by
    positivity
  have hnum : |2 * x| ≤ 1 + x ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [sq_nonneg (|x| - 1), sq_abs x]
  have hA :
      |2 * x / (1 + x ^ 2) ^ 2| ≤
        1 / (1 + x ^ 2) := by
    rw [abs_div, abs_of_pos (sq_pos_of_pos hd)]
    calc
      |2 * x| / (1 + x ^ 2) ^ 2 ≤
          (1 + x ^ 2) / (1 + x ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = 1 / (1 + x ^ 2) := by
        field_simp
  have hB :
      |(2 * x / (1 + x ^ 2) ^ 2) *
        Real.sin (1 / x)| ≤ 1 / (1 + x ^ 2) := by
    rw [abs_mul]
    calc
      |2 * x / (1 + x ^ 2) ^ 2| *
          |Real.sin (1 / x)| ≤
          (1 / (1 + x ^ 2)) * 1 :=
        mul_le_mul hA hs (abs_nonneg _) (by positivity)
      _ = 1 / (1 + x ^ 2) := by ring
  have hsin :
      -(1 / (1 + x ^ 2)) ≤
        (2 * x / (1 + x ^ 2) ^ 2) *
          Real.sin (1 / x) := by
    exact (abs_le.mp hB).1
  have hcos :
      (1 / (1 + x ^ 2)) * Real.cos (1 / x) ≤
        1 / (1 + x ^ 2) := by
    calc
      (1 / (1 + x ^ 2)) * Real.cos (1 / x) ≤
          (1 / (1 + x ^ 2)) * 1 :=
        mul_le_mul_of_nonneg_left hc
          (div_nonneg (by norm_num) (le_of_lt hd))
      _ = 1 / (1 + x ^ 2) := by ring
  have hden : 1 / (1 + x ^ 2) ≤ 1 := by
    rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg x]
  linarith
/-- The derivative is nonnegative everywhere. -/
private theorem deriv_nonneg (x : ℝ) :
    0 ≤ deriv monotoneDiscontinuousDerivFn x := by
  by_cases hx : x = 0
  · subst x
    rw [deriv_zero]
    norm_num
  · rw [deriv_ne_zero x hx]
    have h := derivativeFormula_ge_one x
    linarith
/-- The constructed function is differentiable at every real number. -/
private theorem differentiableAt_constructedFunction (x : ℝ) :
    DifferentiableAt ℝ monotoneDiscontinuousDerivFn x := by
  by_cases hx : x = 0
  · subst x
    exact hasDerivAt_zero.differentiableAt
  · exact (hasDerivAt_ne_zero x hx).differentiableAt
/-- The constructed function is monotone. -/
private theorem monotone_constructedFunction :
    Monotone monotoneDiscontinuousDerivFn := by
  apply monotone_of_deriv_nonneg
  · intro x
    exact differentiableAt_constructedFunction x
  · exact deriv_nonneg
/-- The derivative of the constructed function is not continuous. -/
private theorem deriv_not_continuous :
    ¬ Continuous (deriv monotoneDiscontinuousDerivFn) := by
  intro hcont
  let x : ℕ → ℝ := fun n =>
    (1 / (2 * Real.pi)) * (1 / ((n : ℝ) + 1))
  have hseq : Filter.Tendsto x Filter.atTop (nhds 0) := by
    dsimp [x]
    simpa using
      (tendsto_const_nhds.mul
        (tendsto_one_div_add_atTop_nhds_zero_nat :
          Filter.Tendsto
            (fun n : ℕ => 1 / ((n : ℝ) + 1))
            Filter.atTop (nhds 0)))
  have hxpos (n : ℕ) : 0 < x n := by
    dsimp [x]
    positivity
  have hxne (n : ℕ) : x n ≠ 0 :=
    (hxpos n).ne'
  have harg (n : ℕ) :
      1 / x n = ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by
    dsimp [x]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hderiv (n : ℕ) :
      deriv monotoneDiscontinuousDerivFn (x n) =
        3 - 1 / (1 + (x n) ^ 2) := by
    rw [deriv_ne_zero (x n) (hxne n)]
    unfold derivativeFormula
    rw [harg n]
    have hs : Real.sin ((↑(n + 1) : ℝ) * (2 * Real.pi)) = 0 := by
      convert Real.sin_nat_mul_pi (2 * (n + 1)) using 1 ;
        push_cast ; ring_nf
    have hc : Real.cos ((↑(n + 1) : ℝ) * (2 * Real.pi)) = 1 := by
      exact Real.cos_nat_mul_two_pi (n + 1)
    rw [hs, hc]
    ring
  have hfac : 1 / (2 * Real.pi) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    nlinarith [Real.two_le_pi]
  have hfac2 (n : ℕ) :
      1 / ((n : ℝ) + 1) ≤ 1 := by
    apply (div_le_one (by positivity)).2
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    exact hn
  have hxle (n : ℕ) : x n ≤ 1 := by
    dsimp [x]
    calc
      (1 / (2 * Real.pi)) * (1 / ((n : ℝ) + 1))
          ≤ 1 * 1 :=
        mul_le_mul hfac (hfac2 n) (by positivity) (by positivity)
      _ = 1 := by ring
  have hx2 (n : ℕ) : (x n) ^ 2 ≤ 1 := by
    nlinarith [
      mul_nonneg
        (sub_nonneg.mpr (hxle n))
        (show 0 ≤ 1 + x n by positivity)
    ]
  have hrecip (n : ℕ) :
      (1 : ℝ) / 2 ≤ 1 / (1 + (x n) ^ 2) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hx2 n]
  have hbound (n : ℕ) :
      deriv monotoneDiscontinuousDerivFn (x n) ≤ 5 / 2 := by
    rw [hderiv n]
    linarith [hrecip n]
  have hcontseq :
      Filter.Tendsto
        (fun n : ℕ => deriv monotoneDiscontinuousDerivFn (x n))
        Filter.atTop (nhds 3) := by
    simpa only [Function.comp_def, deriv_zero] using
      hcont.continuousAt.tendsto.comp hseq
  have heventually :
      ∀ᶠ n : ℕ in Filter.atTop,
        (5 / 2 : ℝ) <
          deriv monotoneDiscontinuousDerivFn (x n) :=
    hcontseq.eventually
      (Ioi_mem_nhds (by norm_num : (5 / 2 : ℝ) < 3))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  have hlarge :=
    hN N le_rfl
  have hsmall :=
    hbound N
  linarith

end MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv

namespace MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDerivWanted

open MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDeriv

/-- **A monotone differentiable function with discontinuous derivative.** There is a
nondecreasing function $f : \mathbb{R} \to \mathbb{R}$ that is differentiable at every point and
whose derivative $f'$ is not continuous.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_92.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_monotone_differentiable_not_continuous_deriv :
    ∃ f : ℝ → ℝ,
      Monotone f ∧
      (∀ x : ℝ, DifferentiableAt ℝ f x) ∧
      ¬ Continuous (deriv f) := by
  refine ⟨monotoneDiscontinuousDerivFn,
    monotone_constructedFunction, ?_, deriv_not_continuous⟩
  intro x
  exact differentiableAt_constructedFunction x

end MathlibExt.Analysis.Calculus.MonotoneDiscontinuousDerivWanted
