/-
# The inf-convolution g_n(x) = inf_p f(p) + n·d(x,p) is n-Lipschitz

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_36.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l1_36 … := by sorry` into the Batteries `theorem_wanted`
`abs_toReal_g_sub_le_mul_dist`; moved the informal problem statement docstring onto it and
placed the declarations in namespace `MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted`;
replaced `import Mathlib` by `public import Mathlib` under the module system; added docstrings
to helper definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted

variable {X : Type*} [MetricSpace X]

/-- **Inf-convolution with a multiple of the distance.** Let $X$ be a metric space with metric
$d$, let $f : X \to [0,\infty]$, and let $n$ be a natural number. For $x \in X$,
$$
g_n(x) = \inf\{f(p) + n\,d(x,p) : p \in X\},
$$
the infimum being taken in $[0,\infty]$.
-/
noncomputable def g (f : X → ENNReal) (n : ℕ) (x : X) : ENNReal :=
  sInf (Set.range fun p : X => f p + n * ENNReal.ofReal (dist x p))

/-- **The inf-convolution of a lower semicontinuous function is Lipschitz.** Let $X$ be a metric
space with metric $d$, and let $f : X \to [0,\infty]$ be lower semicontinuous with $f(p) < \infty$
for at least one $p \in X$. For a natural number $n$ and $x \in X$ let
$$
g_n(x) = \inf\{f(p) + n\,d(x,p) : p \in X\} \in [0,\infty].
$$
Then $|g_n(x) - g_n(y)| \le n\,d(x,y)$ for every natural number $n$ (including $n = 0$) and all
$x, y \in X$.

Each $g_n(x)$ is finite, since $g_n(x) \le f(p) + n\,d(x,p)$ for the point $p$ with
$f(p) < \infty$, so the difference is one of real numbers.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functional analysis; Nonlinear
functional analysis), `benchmark/level1/ma_proofbench_l1_36.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted abs_toReal_g_sub_le_mul_dist (f : X → ENNReal) (hf : LowerSemicontinuous f)
    (hp : ∃ p : X, f p < ⊤)
    (n : ℕ) (x y : X) :
    |(g f n x).toReal - (g f n y).toReal| ≤ n * dist x y

end MathlibExt.MeasureTheory.InfConvolutionLipschitzWanted
