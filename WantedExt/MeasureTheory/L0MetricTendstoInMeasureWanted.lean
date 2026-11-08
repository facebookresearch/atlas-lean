/-
# L^0 metric convergence is convergence in measure

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_07.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_07 … := by sorry` into the Batteries `theorem_wanted`
`tendsto_L0PseudoMetric_zero_iff_tendstoInMeasure`; moved the informal problem statement
docstring onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.L0MetricTendstoInMeasureWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system; added docstrings to helper definitions; renamed the
helper `L0Metric` to `L0PseudoMetric` and documented that `L⁰([0, 1])` is represented by
measurable functions, on which the source's metric is a pseudometric; the convergence claim
depends only on a.e.-classes on `[0, 1]`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open scoped Topology

namespace MathlibExt.MeasureTheory.L0MetricTendstoInMeasureWanted

/-- Measurable real functions on `ℝ`, used as representatives of `L⁰([0, 1])`; nothing below depends
on their values off `[0, 1]` or on a null set. -/
abbrev L0UnitInterval : Type := {f : ℝ → ℝ // Measurable f}

/-- `∫ x in [0, 1], |f x - g x| / (1 + |f x - g x|)`. On representatives this is a pseudometric
(functions that agree a.e. on `[0, 1]` are at distance `0`); it is the source's metric `d` on the
a.e.-classes of `L⁰([0, 1])`. -/
noncomputable def L0PseudoMetric (f g : L0UnitInterval) : ℝ :=
  ∫ x, |f.1 x - g.1 x| / (1 + |f.1 x - g.1 x|)
    ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Let $L^0([0,1])$ be the vector space of Lebesgue measurable functions. Let $d$ be the metric on
$L^0([0,1])$ given by
\[
d(f,g) = \int_0^1 \frac{|f-g|(x)}{1 + |f-g|(x)}\,dx.
\]
Prove that $f_n \to f$ in the metric $d$ if and only if $f_n \to f$ in measure.

Lean variant: `L⁰([0, 1])` is represented by measurable functions on `ℝ`, so `L0PseudoMetric` is the
source's metric `d` read on representatives (a pseudometric there); both sides of the equivalence
depend only on the a.e.-classes on `[0, 1]`.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_07.lean` at
openbmb/ma-proofbench@31bab4c, with the change above.
-/
public theorem_wanted tendsto_L0PseudoMetric_zero_iff_tendstoInMeasure
    (fSeq : ℕ → L0UnitInterval) (f : L0UnitInterval) :
    Filter.Tendsto (fun n => L0PseudoMetric (fSeq n) f) Filter.atTop (𝓝 (0 : ℝ)) ↔
      MeasureTheory.TendstoInMeasure
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))
        (fun n x => (fSeq n).1 x) Filter.atTop (fun x => f.1 x)

end MathlibExt.MeasureTheory.L0MetricTendstoInMeasureWanted
