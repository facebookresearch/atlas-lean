/-
# Positive Fourier decay of a circle measure extends to L^1 densities

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_13.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_13 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_integral_pow_mul_of_tendsto_integral_pow`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted

/-- **Fourier decay of a circle measure passes to integrable densities.** Let $\mu$ be a finite
Borel measure on $\mathbb{C}$ concentrated on the unit circle $T = \{z \in \mathbb{C} : |z| = 1\}$,
that is, $\mu$-almost every $z$ lies in $T$, and suppose that $\int z^n \, d\mu(z) \to 0$ as
$n \to \infty$ through $\mathbb{N}$. Then for every $\mu$-integrable function
$f : \mathbb{C} \to \mathbb{C}$,
$$
\lim_{n \to \infty} \int z^n f(z) \, d\mu(z) = 0.
$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Set
functions and measures on spaces with additional structure),
`benchmark/level2/ma_proofbench_l2_13.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted tendsto_integral_pow_mul_of_tendsto_integral_pow
    (μ : MeasureTheory.Measure ℂ)
    (hfinite : μ Set.univ < ⊤)
    (hsphere : ∀ᵐ z ∂μ, z ∈ Metric.sphere (0 : ℂ) 1)
    (hpow : Filter.Tendsto (fun n : ℕ => ∫ z, z ^ n ∂μ) Filter.atTop (nhds 0))
    (f : ℂ → ℂ)
    (hf : MeasureTheory.Integrable f μ) :
    Filter.Tendsto (fun n : ℕ => ∫ z, z ^ n * f z ∂μ) Filter.atTop (nhds 0)

end MathlibExt.MeasureTheory.CircleMeasureFourierDecayIntegrableWanted
