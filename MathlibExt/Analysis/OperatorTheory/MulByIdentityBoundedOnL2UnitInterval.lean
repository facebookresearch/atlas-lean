/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_31.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029, byte-identical to the Hugging Face dataset
openbmb/MA-ProofBench; L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782):
Copyright (c) 2026 OpenBMB.
Licensed under the MIT License:

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

Authors (of MA-ProofBench, as listed on arXiv:2606.13782): Lushi Pu, Weiming Zhang, Xinheng Xie,
Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li, Jie Zhou, Yudong Wang.

The adapted portion is the statement of `exists_continuousLinearMap_mul_id_L2_Icc`, formerly the
`theorem_wanted` of the same name in
`WantedExt/Analysis/OperatorTheory/MulByIdentityBoundedOnL2UnitIntervalWanted.lean`, whose notice
recorded these changes from the source: converted `theorem ma_proofbench_l1_31 … := by sorry`
into the Batteries `theorem_wanted` `exists_continuousLinearMap_mul_id_L2_Icc`; moved the
informal problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted`; replaced
`import Mathlib` by `public import Mathlib` under the module system. Further changes in this
file: the `theorem_wanted` is now a `theorem` with a proof, `public import Mathlib` is replaced
by narrower imports, and the source's informal problem statement, which the wanted entry carried
as its docstring, is replaced by a restatement of the theorem in words (a bounded linear operator
that agrees almost everywhere with `t f(t)`); the name, namespace and statement are unchanged.
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Holder

/-!
# Multiplication by `t` is a bounded operator on `L²([0, 1])`

Let `μ` be Lebesgue measure restricted to `[0, 1]`. For every `f ∈ L²(μ)` the function
`t ↦ t f(t)` is again in `L²(μ)`, and `(T f)(t) = t f(t)` defines a bounded linear operator `T`
on `L²(μ)`. Since `|t| ≤ 1` on `[0, 1]`, `∫ |t f(t)|² dμ ≤ ∫ |f(t)|² dμ`, so `‖T‖ ≤ 1`. Such an
operator is unique, because an element of `L²(μ)` is determined by its values almost everywhere.

## Proof

The coordinate function `t ↦ t` is bounded by `1` on `[0, 1]`, so it defines an element `g` of
`L^∞(μ)`. By Hölder's inequality for the exponents `∞`, `2`, `2`, multiplication
`ℝ →L[ℝ] ℝ →L[ℝ] ℝ` induces a continuous bilinear map `L^∞(μ) → L²(μ) → L²(μ)`
(`ContinuousLinearMap.holderL`), and `T` is this map with first argument `g`. Its value at `f` is
almost everywhere the pointwise product of representatives of `g` and `f`
(`ContinuousLinearMap.coeFn_holder`), that is, `t f(t)` for almost every `t`.

## Main results

* `exists_continuousLinearMap_mul_id_L2_Icc`: there is a continuous linear map `T` on
  `L²([0, 1])` such that `(T f)(t) = t f(t)` for almost every `t ∈ [0, 1]`.

The statement is the MA-ProofBench problem `ma_proofbench_l1_31`; it keeps the name and the
namespace it had as a `WantedExt` entry.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted

/-- **Multiplication by $t$ is bounded on $L^2([0,1])$.** Let $L^2([0,1])$ be the space of real
square-integrable functions for Lebesgue measure on $[0,1]$. There is a bounded linear operator
$T : L^2([0,1]) \to L^2([0,1])$ such that for every $f \in L^2([0,1])$, $(Tf)(t) = t f(t)$ for
almost every $t \in [0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Operator theory; General theory
of linear operators), `benchmark/level1/ma_proofbench_l1_31.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_continuousLinearMap_mul_id_L2_Icc :
    ∃ T : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) →L[ℝ]
        Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1)),
        ((T f : Lp ℝ 2 (volume.restrict (Set.Icc (0 : ℝ) 1))) : ℝ → ℝ)
          =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
            fun t => t * (f : ℝ → ℝ) t := by
  -- The coordinate function is bounded by `1` on `[0, 1]`, so it lies in `L^∞`.
  have hg : MemLp (fun t : ℝ => t) ∞ (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    memLp_top_of_bound continuous_id.aestronglyMeasurable 1
      (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [ht.1], ht.2⟩)
  -- Hölder's inequality for `∞, 2, 2`: multiplication by an `L^∞` function is bounded on `L²`.
  refine ⟨(ContinuousLinearMap.mul ℝ ℝ).holderL _ ∞ 2 2 hg.toLp, fun f => ?_⟩
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2) hg.toLp f, hg.coeFn_toLp]
    with t hT hgt
  rw [ContinuousLinearMap.holderL_apply_apply, hT, ContinuousLinearMap.mul_apply', hgt]

end MathlibExt.Analysis.OperatorTheory.MulByIdentityBoundedOnL2UnitIntervalWanted
