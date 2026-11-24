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

/-- **Measurable functions representing $L^0([0,1])$.** The type of Borel measurable functions
$f : \mathbb{R} \to \mathbb{R}$, used as representatives of the elements of $L^0([0,1])$.

The pseudometric and the convergence in measure built on them depend only on the restriction
of $f$ to $[0,1]$ up to a null set.
-/
abbrev L0UnitInterval : Type := {f : ℝ → ℝ // Measurable f}

/-- **The $L^0$ pseudometric on $[0,1]$.** For Borel measurable functions
$f, g : \mathbb{R} \to \mathbb{R}$,
$$
d(f,g) = \int_{[0,1]} \frac{|f(x) - g(x)|}{1 + |f(x) - g(x)|}\,dx,
$$
the integral being with respect to Lebesgue measure on $[0,1]$.

This is a pseudometric: functions that agree almost everywhere on $[0,1]$ are at distance $0$,
and on the almost-everywhere classes it is the usual metric of $L^0([0,1])$.
-/
noncomputable def L0PseudoMetric (f g : L0UnitInterval) : ℝ :=
  ∫ x, |f.1 x - g.1 x| / (1 + |f.1 x - g.1 x|)
    ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/-- **Convergence in the $L^0$ pseudometric is convergence in measure.** Let $f$ and
$f_0, f_1, f_2, \ldots$ be Borel measurable functions $\mathbb{R} \to \mathbb{R}$, and let $d$ be
the pseudometric
$$
d(g,h) = \int_{[0,1]} \frac{|g(x) - h(x)|}{1 + |g(x) - h(x)|}\,dx
$$
on such functions, the integral being with respect to Lebesgue measure. Then
$d(f_n, f) \to 0$ as $n \to \infty$ if and only if $f_n \to f$ in measure with respect to
Lebesgue measure on $[0,1]$: for every $\varepsilon > 0$, the Lebesgue measure of
$\{x \in [0,1] : |f_n(x) - f(x)| \ge \varepsilon\}$ tends to $0$ as $n \to \infty$.

The source states this for $L^0([0,1])$, on which $d$ is a metric; here it is stated for
representatives, on which $d$ is only a pseudometric. Both sides depend only on the
almost-everywhere classes of the functions on $[0,1]$, so the two statements say the same thing.

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
