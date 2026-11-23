/-
# Multiplication by x on L^2([1,2]) is bounded, invertible, self-adjoint

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level2/ma_proofbench_l2_26.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782; byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench), distributed under the MIT License above. Changes made: converted
`theorem ma_proofbench_l2_26 … := by sorry` into the Batteries `theorem_wanted`
`continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two`; moved the informal problem
statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjointWanted`; replaced `import
Mathlib` by `public import Mathlib` under the module system; added docstrings to helper
definitions.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjointWanted

/-- **The space $L^2([1,2])$.** $L^2([1,2])$ is the space of real-valued functions on
$\mathbb{R}$ that are square-integrable for Lebesgue measure restricted to $[1,2]$, taken modulo
equality almost everywhere on $[1,2]$. -/
noncomputable abbrev L2OnOneTwo : Type :=
  (ℝ →₂[volume.restrict (Set.Icc (1 : ℝ) 2)] ℝ)

/-- **Multiplication by $x$ on $L^2([1,2])$ is bounded, bijective and self-adjoint.** Let
$L^2([1,2])$ be the real Hilbert space of square-integrable real functions for Lebesgue measure
on $[1,2]$, with inner product $\langle f, g\rangle = \int_1^2 f(x)g(x)\,dx$. Let
$T : L^2([1,2]) \to L^2([1,2])$ be a linear map such that for every $f$, $(Tf)(x) = x f(x)$ for
almost every $x \in [1,2]$. Then $T$ is continuous and bijective, and $T = T^*$, where $T^*$ is
the Hilbert space adjoint of $T$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Operator theory; General
theory of linear operators), `benchmark/level2/ma_proofbench_l2_26.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem_wanted continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two
    (T : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo)
    (hT : ∀ f : L2OnOneTwo,
      T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x) :
    Continuous T ∧ Function.Bijective T ∧
      ∃ Tc : L2OnOneTwo →L[ℝ] L2OnOneTwo,
        Tc.toLinearMap = T ∧ Tc.adjoint = Tc

end MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjointWanted
