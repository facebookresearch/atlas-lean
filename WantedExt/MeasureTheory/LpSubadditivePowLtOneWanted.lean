/-
# ∫||f|^p − |g|^p| ≤ ∫|f − g|^p for 0 < p < 1

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_53.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_53 … := by sorry` into the Batteries `theorem_wanted`
`integral_abs_rpow_sub_rpow_le_integral_rpow_abs_sub`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted

/-- **An integral inequality for $p$-th powers with $0 < p < 1$.** Let $\mu$ be a measure on a
measurable space and let $0 < p < 1$. Then for all real-valued $f, g \in L^p(\mu)$,
$$\int \bigl||f|^p - |g|^p\bigr|\,d\mu \le \int |f - g|^p\,d\mu.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Linear
function spaces and their duals), `benchmark/level1/ma_proofbench_l1_53.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted integral_abs_rpow_sub_rpow_le_integral_rpow_abs_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal} (hp0 : 0 < p) (hp1 : p < 1)
    {f g : Lp ℝ p μ} :
    (∫ x, |((|f x|) ^ p.toReal) - ((|g x|) ^ p.toReal)| ∂μ) ≤
      ∫ x, (|f x - g x|) ^ p.toReal ∂μ

end MathlibExt.MeasureTheory.LpSubadditivePowLtOneWanted
