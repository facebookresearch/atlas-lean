/-
# Uniformly large level sets under an L^2 <= C L^1 bound

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_04.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_04 … := by sorry` into the Batteries `theorem_wanted`
`exists_tendsto_atTop_inf_measure_levelSet_pos`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions;
corrected the statement: replaced the target filter `atTop` of the divergence hypothesis
`hL1_div` by `nhds ⊤`; in `ℝ≥0∞`, `atTop = pure ⊤`, so the source hypothesis forced `‖f n‖₁ = ∞`
eventually, contradicting `MemLp (f n) 2`, and made the statement vacuous.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted

/-- Lebesgue measure restricted to `[0, 1]`. -/
noncomputable abbrev μIcc01 : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Let $\{f_n\}_{n=1}^\infty\subset L^2([0,1])$. Suppose $\|f_n\|_{L^2}\le 2024\|f_n\|_{L^1}$ for
all $n\in\mathbb{Z}_{>0}$.
If $\lim_{n\to\infty}\|f_n\|_{L^1}=\infty$, prove that there exists a sequence $y_n\to\infty$ such
that
\[
\inf_n |\{x: |f_n(x)|\ge y_n\}|>0.
\]

Lean variant: the source writes `Tendsto (fun n => eLpNorm (f n) 1 μ) atTop atTop` in `ℝ≥0∞`, where
`atTop = pure ⊤`; that hypothesis forces `‖f n‖₁ = ∞` eventually and contradicts `MemLp (f n) 2`, so
the statement was vacuous. The target filter is `nhds ⊤` here, the intended `‖f n‖₁ → ∞`.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_04.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
public theorem_wanted exists_tendsto_atTop_inf_measure_levelSet_pos
    (f : ℕ → ℝ → ℝ)
    (hf_L2 : ∀ n : ℕ, MemLp (f n) 2 μIcc01)
    (hbound : ∀ n : ℕ,
      eLpNorm (f n) 2 μIcc01 ≤
        ENNReal.ofReal 2024 * eLpNorm (f n) 1 μIcc01)
    (hL1_div : Tendsto (fun n : ℕ => eLpNorm (f n) 1 μIcc01) atTop (nhds ⊤)) :
    ∃ y : ℕ → ℝ,
      Tendsto y atTop atTop ∧
      0 < sInf (Set.range (fun n : ℕ =>
        μIcc01 {x : ℝ | |f n x| ≥ y n}))

end MathlibExt.MeasureTheory.LargeLevelSetReverseHolderWanted
