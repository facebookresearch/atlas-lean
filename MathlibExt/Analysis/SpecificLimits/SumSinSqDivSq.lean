/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_03.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029; MA-ProofBench, L. Pu et al., arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

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

Attribution and modification notice: the statement of `tsum_sin_sq_mul_div_sq_mul` below is taken
from openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level1/ma_proofbench_l1_03.lean` (MA-ProofBench, L. Pu et al., *MA-ProofBench: A
Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782;
byte-identical to the Hugging Face dataset openbmb/MA-ProofBench), distributed under the MIT
License above. Changes made: converted the benchmark theorem `ma_proofbench_l1_03`, whose proof
there is a placeholder, into the Batteries wanted-theorem declaration `tsum_sin_sq_mul_div_sq_mul`
(a statement without a proof); moved the informal problem statement docstring onto it and placed
the declarations in namespace `MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system. Further changes in this file:
that wanted declaration is now a `theorem` with a proof, and `public import Mathlib` is replaced by
narrower imports; the statement and its docstring are unchanged.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ZetaValues

/-!
# A closed form for the series of `sin² (n δ) / (n² δ)`

For every real `δ` with `0 < δ < π`,
`∑_{n ≥ 1} sin² (n δ) / (n² δ) = (π - δ) / 2`.

Since `sin² θ = (1 - cos (2 θ)) / 2`, the series `∑ sin² (n δ) / n²` is half the difference of
`∑ 1 / n² = π² / 6` (`hasSum_zeta_two`) and `∑ cos (2 n δ) / n²`. The Fourier series of the
Bernoulli polynomial `B₂ (x) = x² - x + 1 / 6` (`hasSum_one_div_nat_pow_mul_cos`) gives
`∑ cos (n x) / n² = π² / 6 - π x / 2 + x² / 4` for `0 ≤ x ≤ 2 π`, hence
`∑ sin² (n δ) / n² = δ (π - δ) / 2` for `0 ≤ δ ≤ π`. Dividing by `δ`, and dropping the term at
`n = 0`, which vanishes, gives the closed form.

## Main statements

* `tsum_sin_sq_mul_div_sq_mul`: the closed form above. This is the MA-ProofBench problem
  `ma_proofbench_l1_03`, formerly a `WantedExt` entry.

## References

* L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem Proving in
  Mathematical Analysis*, arXiv:2606.13782, Level I, problem `ma_proofbench_l1_03`.
-/

@[expose] public section

namespace MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted

open Real

/-- For `0 ≤ x ≤ 2 π`, `∑ cos (n x) / n² = π² / 6 - π x / 2 + x² / 4`: the Fourier series of the
Bernoulli polynomial `B₂ (y) = y² - y + 1 / 6`, evaluated at `y = x / (2 π)`. -/
private theorem hasSum_cos_mul_div_sq {x : ℝ} (hx0 : 0 ≤ x) (hx2pi : x ≤ 2 * π) :
    HasSum (fun n : ℕ => cos (n * x) / (n : ℝ) ^ 2) (π ^ 2 / 6 - π * x / 2 + x ^ 2 / 4) := by
  have hx : x / (2 * π) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one (by positivity)).2 hx2pi⟩
  -- The value of `B₂` at `x / (2 π)`, as it appears in `hasSum_one_div_nat_pow_mul_cos`.
  have hB : (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1))).eval (x / (2 * π)) =
      (x / (2 * π)) ^ 2 - x / (2 * π) + 6⁻¹ :=
    bernoulliFun_two _
  convert hasSum_one_div_nat_pow_mul_cos one_ne_zero hx using 1
  · ext n
    rw [show 2 * π * n * (x / (2 * π)) = n * x by field_simp, one_div_mul_eq_div, mul_one]
  · rw [hB, show (Nat.factorial (2 * 1) : ℝ) = 2 by norm_num [Nat.factorial]]
    field_simp
    ring

/-- For `0 ≤ δ ≤ π`, `∑ sin² (n δ) / n² = δ (π - δ) / 2`. -/
private theorem hasSum_sin_sq_mul_div_sq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδpi : δ ≤ π) :
    HasSum (fun n : ℕ => sin (n * δ) ^ 2 / (n : ℝ) ^ 2) (δ * (π - δ) / 2) := by
  -- `sin² (n δ) = 1 / 2 - cos (n (2 δ)) / 2`, and `0 ≤ 2 δ ≤ 2 π`.
  have h := (hasSum_zeta_two.sub
    (hasSum_cos_mul_div_sq (x := 2 * δ) (by positivity) (by linarith))).div_const 2
  convert h using 1
  · ext n
    rw [sin_sq_eq_half_sub, mul_left_comm 2 (n : ℝ) δ]
    ring
  · ring

/-- **A closed form for $\sum \sin^2(n\delta)/(n^2\delta)$.** For every real $\delta$ with
$0 < \delta < \pi$,

$$\sum_{n=1}^{\infty} \frac{\sin^2(n\delta)}{n^2\delta} = \frac{\pi - \delta}{2}.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Sequences, series, summability;
Convergence and divergence of infinite limiting processes),
`benchmark/level1/ma_proofbench_l1_03.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem tsum_sin_sq_mul_div_sq_mul
    {δ : ℝ} (hδ0 : 0 < δ) (hδpi : δ < Real.pi) :
    (∑' n : ℕ,
        (Real.sin ((n + 1 : ℕ) * δ)) ^ 2 / (((n + 1 : ℕ) ^ 2) * δ))
      = (Real.pi - δ) / 2 := by
  have h : HasSum (fun n : ℕ => sin (n * δ) ^ 2 / ((n : ℝ) ^ 2 * δ)) ((π - δ) / 2) := by
    convert (hasSum_sin_sq_mul_div_sq hδ0.le hδpi.le).div_const δ using 1
    · simp only [div_div]
    · rw [eq_div_iff hδ0.ne']
      ring
  -- The term at `n = 0` vanishes, so the series from `n = 1` has the same sum.
  have h0 : sin (((0 : ℕ) : ℝ) * δ) ^ 2 / (((0 : ℕ) : ℝ) ^ 2 * δ) = 0 := by simp
  refine ((hasSum_nat_add_iff (f := fun n : ℕ => sin (n * δ) ^ 2 / ((n : ℝ) ^ 2 * δ)) 1).2
    ?_).tsum_eq
  rwa [Finset.sum_range_one, h0, add_zero]

end MathlibExt.Analysis.SpecificLimits.SumSinSqDivSqWanted
