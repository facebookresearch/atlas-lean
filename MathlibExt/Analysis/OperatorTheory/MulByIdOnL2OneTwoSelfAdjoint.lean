/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_26.lean` (openbmb/ma-proofbench at commit
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

The adapted portions are the definition `L2OnOneTwo` and the statement of
`continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two`, formerly in
`WantedExt/Analysis/OperatorTheory/MulByIdOnL2OneTwoSelfAdjointWanted.lean`, whose notice
recorded these changes from the source: converted `theorem ma_proofbench_l2_26 … := by sorry`
into the Batteries `theorem_wanted` `continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two`;
moved the informal problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjointWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system; added docstrings to helper definitions. The
two docstrings were later restated to match the Lean statements: the source's informal problem
statement, which the wanted entry carried as its docstring, became a restatement of the theorem in
words. Further changes in this file: the `theorem_wanted` is now a `theorem` with a proof, and
`public import Mathlib` is replaced by narrower imports; the names, the namespace, the definition
and the statement are unchanged.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Multiplication by `x` on `L²([1, 2])` is bounded, bijective and self-adjoint

Let `μ` be Lebesgue measure restricted to `[1, 2]`, and let `T` be a linear map on `L²(μ)` such
that `(T f)(x) = x f(x)` for almost every `x ∈ [1, 2]`. Then `T` is continuous and bijective, and
it is self-adjoint: as a continuous linear map, it equals its Hilbert space adjoint.

## Proof

Everything follows from `1 ≤ x ≤ 2` for `x ∈ [1, 2]`.

* `‖T f‖ ≤ 2 ‖f‖`, so `T` is continuous (`LinearMap.mkContinuous`).
* If `T f = 0`, then `x f(x) = 0`, hence `f(x) = 0`, for almost every `x`; so `T` is injective.
* For `g ∈ L²(μ)`, the function `x ↦ x⁻¹ g(x)` is in `L²(μ)` because `|x⁻¹| ≤ 1`, and `T` sends
  its class to `g`; so `T` is surjective.
* `⟪T f, g⟫ = ∫ x f(x) g(x) dμ = ⟪f, T g⟫`, so `T` equals its adjoint
  (`ContinuousLinearMap.eq_adjoint_iff`).

## Main results

* `L2OnOneTwo`: the real Hilbert space `L²([1, 2])`.
* `continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two`: a linear map on `L²([1, 2])` that
  multiplies by `x` almost everywhere is continuous, bijective and self-adjoint.

The statement is the MA-ProofBench problem `ma_proofbench_l2_26`; it keeps the names and the
namespace it had as a `WantedExt` entry.
-/

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
theorem continuous_bijective_selfAdjoint_of_mul_id_L2_Icc_one_two
    (T : L2OnOneTwo →ₗ[ℝ] L2OnOneTwo)
    (hT : ∀ f : L2OnOneTwo,
      T f =ᵐ[volume.restrict (Set.Icc (1 : ℝ) 2)] fun x : ℝ => x * f x) :
    Continuous T ∧ Function.Bijective T ∧
      ∃ Tc : L2OnOneTwo →L[ℝ] L2OnOneTwo,
        Tc.toLinearMap = T ∧ Tc.adjoint = Tc := by
  -- Almost every point of `[1, 2]`, for the restricted measure, lies in `[1, 2]`.
  have hmem : ∀ᵐ x ∂(volume.restrict (Set.Icc (1 : ℝ) 2)), x ∈ Set.Icc (1 : ℝ) 2 :=
    ae_restrict_mem measurableSet_Icc
  -- `|x| ≤ 2` on `[1, 2]`, so `‖T f‖ ≤ 2 ‖f‖` and `T` is continuous.
  have hbound : ∀ f : L2OnOneTwo, ‖T f‖ ≤ 2 * ‖f‖ := fun f => by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [hT f, hmem] with x hx hx12
    rw [hx, norm_mul, Real.norm_of_nonneg (by linarith [hx12.1])]
    exact mul_le_mul_of_nonneg_right hx12.2 (norm_nonneg _)
  let Tc : L2OnOneTwo →L[ℝ] L2OnOneTwo := T.mkContinuous 2 hbound
  refine ⟨Tc.continuous, ⟨?_, fun g => ?_⟩, Tc, rfl, ?_⟩
  · -- Injective: `x f(x) = 0` with `x ≠ 0` forces `f(x) = 0`.
    refine (injective_iff_map_eq_zero T).mpr fun f hf => Lp.eq_zero_iff_ae_eq_zero.mpr ?_
    filter_upwards [hT f, hmem, Lp.coeFn_zero ℝ 2 (volume.restrict (Set.Icc (1 : ℝ) 2))]
      with x hx hx12 h0
    rw [hf, h0] at hx
    exact (mul_eq_zero.mp hx.symm).resolve_left (by linarith [hx12.1])
  · -- Surjective: `x ↦ x⁻¹ g(x)` lies in `L²` since `|x⁻¹| ≤ 1`, and `T` sends it to `g`.
    have hinv : MemLp (fun x : ℝ => x⁻¹ * g x) 2 (volume.restrict (Set.Icc (1 : ℝ) 2)) := by
      refine (Lp.memLp g).of_le_mul (c := 1)
        (measurable_inv.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)) ?_
      filter_upwards [hmem] with x hx12
      rw [norm_mul, norm_inv, Real.norm_of_nonneg (by linarith [hx12.1])]
      exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hx12.1) (norm_nonneg _)
    refine ⟨hinv.toLp _, Lp.ext ?_⟩
    filter_upwards [hT (hinv.toLp _), hinv.coeFn_toLp, hmem] with x hx hxg hx12
    rw [hx, hxg, ← mul_assoc, mul_inv_cancel₀ (by linarith [hx12.1]), one_mul]
  · -- Self-adjoint: `⟪T f, g⟫ = ∫ x f(x) g(x) = ⟪f, T g⟫`.
    refine ((ContinuousLinearMap.eq_adjoint_iff Tc Tc).mpr fun f g => ?_).symm
    rw [L2.inner_def, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hT f, hT g] with x hf hg
    simp only [Tc, LinearMap.mkContinuous_apply, hf, hg, RCLike.inner_apply, conj_trivial]
    ring

end MathlibExt.Analysis.OperatorTheory.MulByIdOnL2OneTwoSelfAdjointWanted
