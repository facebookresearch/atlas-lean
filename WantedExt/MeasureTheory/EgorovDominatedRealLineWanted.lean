/-
# Egorov on ℝ for an integrably dominated sequence

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_43.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_43 … := by sorry` into the Batteries `theorem_wanted`
`exists_measure_lt_tendstoUniformlyOn_compl_of_ae_tendsto_of_abs_le`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted

/-- Let $f_n : \mathbb{R} \to \mathbb{R}$, $n \in \mathbb{N}$ be a sequence of Lebesgue measurable
function on $\mathbb{R}$
such that
\begin{itemize}
\item $f_n \to f$ almost everywhere, where $f : \mathbb{R} \to \mathbb{R}$;
\item there exists a Lebesgue integrable function $g : \mathbb{R} \to [0, \infty)$ such that for any
$x \in \mathbb{R}$ and $n \in \mathbb{N}$, $|f_n(x)| \le g(x)$.
\end{itemize}

Show that for any $\varepsilon > 0$, there exists a subset $E \subset \mathbb{R}$ with Lebesgue
measure
$m(E) < \varepsilon$ such that $f_n$ converges uniformly to $f$ on $\mathbb{R} \setminus E$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration;
Classical measure theory), `benchmark/level2/ma_proofbench_l2_43.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted exists_measure_lt_tendstoUniformlyOn_compl_of_ae_tendsto_of_abs_le
  (f : ℝ → ℝ) (fn : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (hfn_meas : ∀ n : ℕ, Measurable (fn n))
  (hae : ∀ᵐ x ∂MeasureTheory.volume, Filter.Tendsto (fun n : ℕ => fn n x) Filter.atTop (nhds (f x)))
  (hg : MeasureTheory.Integrable g)
  (hdom : ∀ n : ℕ, ∀ x : ℝ, |fn n x| ≤ g x) :
  ∀ ε : ℝ, ε > 0 → ∃ E : Set ℝ,
    MeasurableSet E ∧ MeasureTheory.volume E < ENNReal.ofReal ε ∧
      TendstoUniformlyOn fn f Filter.atTop Eᶜ

end MathlibExt.MeasureTheory.EgorovDominatedRealLineWanted
