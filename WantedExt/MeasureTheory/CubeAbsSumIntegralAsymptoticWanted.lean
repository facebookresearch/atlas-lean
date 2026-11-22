/-
# Integral of |x_1+…+x_n| over the unit cube is ~ √(n/(6π))

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_95.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_95 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_abs_sum_cube_div_sqrt`; moved the informal problem statement docstring onto it
and placed the declarations in namespace
`MathlibExt.MeasureTheory.CubeAbsSumIntegralAsymptoticWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Topology Filter

namespace MathlibExt.MeasureTheory.CubeAbsSumIntegralAsymptoticWanted

/-- Let $I_n$ be the integral of $\left|\sum_{i=1}^n x_i\right|$ over the unit $n$-cube $-1/2\le
x_i\le 1/2$. Prove that $n^{-1/2}I_n\to (6\pi)^{-1/2}$ as $n\to\infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_95.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_integral_abs_sum_cube_div_sqrt
    (I : ℕ → ℝ)
    (hI : ∀ n : ℕ,
      I n = ∫ x in (Set.Icc
          (fun _ : Fin n => (-1 / 2 : ℝ))
          (fun _ : Fin n => (1 / 2 : ℝ))),
        |∑ i : Fin n, x i|) :
    Tendsto (fun n : ℕ => I n / Real.sqrt (n : ℝ)) atTop
      (𝓝 (1 / Real.sqrt (6 * Real.pi)))

end MathlibExt.MeasureTheory.CubeAbsSumIntegralAsymptoticWanted
