/-
# Lp functions with integral over [0,L] tending to 0 form a Borel set

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_25.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_25 … := by sorry` into the Batteries `theorem_wanted`
`measurableSet_vanishingIntegralSet`; moved the informal problem statement docstring onto it and
placed the declarations in namespace
`MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system; added docstrings to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open Filter MeasureTheory

namespace MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted

/-- **Functions with vanishing integrals over $[0, L]$.** For $0 \le p \le \infty$, this is the set
of real-valued $f \in L^p(\mathbb{R})$ (with respect to Lebesgue measure) such that
$\int_{[0, L]} f(x)\,dx \to 0$ as $L \to +\infty$, where the integral of a function that is not
integrable on $[0, L]$ counts as $0$. -/
def vanishingIntegralSet (p : ENNReal) : Set (Lp ℝ p (volume : Measure ℝ)) :=
  {f |
    Tendsto
      (fun L : ℝ => ∫ x in Set.Icc (0 : ℝ) L, f x ∂(volume : Measure ℝ))
      atTop (nhds 0)}

/-- **$L^p$ functions whose integrals over $[0, L]$ tend to $0$ form a Borel set.** Let
$1 \le p \le \infty$. The set of real-valued $f \in L^p(\mathbb{R})$ (with respect to Lebesgue
measure) such that $\int_0^L f(x)\,dx \to 0$ as $L \to +\infty$ is a Borel subset of
$L^p(\mathbb{R})$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Measure and integration; Set
functions, measures and integrals with values in abstract spaces),
`benchmark/level2/ma_proofbench_l2_25.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted measurableSet_vanishingIntegralSet
  (p : ENNReal)
  [Fact ((1 : ENNReal) ≤ p)] :
  @MeasurableSet (Lp ℝ p (volume : Measure ℝ))
    (borel (Lp ℝ p (volume : Measure ℝ)))
    (vanishingIntegralSet p)

end MathlibExt.MeasureTheory.LpVanishingHalfLineIntegralBorelWanted
