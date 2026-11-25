/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_02.lean` (openbmb/ma-proofbench at commit
31bab4c78fd1b0c464e767d62e9202163d1e9029; MA-ProofBench, L. Pu et al., arXiv:2606.13782):
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

Attribution and modification notice: the statement of `exists_continuous_mul_add_of_fderiv_eq`
below is taken from openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level1/ma_proofbench_l1_02.lean` (MA-ProofBench, L. Pu et al., *MA-ProofBench: A
Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782;
byte-identical to the Hugging Face dataset openbmb/MA-ProofBench), distributed under the MIT
License above. Changes made: converted the benchmark theorem `ma_proofbench_l1_02`, whose proof
there is a placeholder, into the Batteries wanted-theorem declaration
`exists_continuous_mul_add_of_fderiv_eq` (a statement without a proof); moved the informal
problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system. Further changes in this file: that wanted
declaration is now a `theorem` with a proof, and `public import Mathlib` is replaced by narrower
imports; the statement and its docstring are unchanged.
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Equal partial derivatives give a factor `x + y`

Let `f : ℝ × ℝ → ℝ` be differentiable with equal partial derivatives, `∂₁f = ∂₂f`, and with
`f (0, 0) = 0`. Then `f (x, y) = g (x, y) * (x + y)` for a continuous `g : ℝ × ℝ → ℝ`.

The derivative of `f` in the direction `(1, -1)` is `∂₁f - ∂₂f = 0`, so `f` is constant on each
line `x + y = c` (`is_const_of_deriv_eq_zero` applied to `t ↦ f (x + t, y - t)`), that is,
`f (x, y) = h (x + y)` with `h t = f (t, 0)`. Since `h` is differentiable and `h 0 = 0`, we have
`h t = t * dslope h 0 t`, where the slope `dslope h 0 t` is `h t / t` for `t ≠ 0` and `h' 0` for
`t = 0`, and it is continuous in `t` (`continuousOn_dslope`). So `g (x, y) = dslope h 0 (x + y)`
works.

## Main results

* `apply_eq_apply_add_zero_of_fderiv_eq`: a differentiable `f : ℝ × ℝ → E` with equal partial
  derivatives satisfies `f (x, y) = f (x + y, 0)`.
* `exists_continuous_mul_add_of_differentiable`: the factorization for a differentiable `f`.
* `exists_continuous_mul_add_of_fderiv_eq`: the factorization for a continuously differentiable
  `f`. This is the MA-ProofBench problem `ma_proofbench_l1_02`, formerly a `WantedExt` entry.

## Implementation notes

`Mathlib.Analysis.InnerProductSpace.Basic` is imported publicly so that the statement of
`exists_continuous_mul_add_of_fderiv_eq` elaborates to the same term as under `import Mathlib`,
where it was first stated: the instance `NormedSpace ℝ ℝ` is then found through
`RCLike.toInnerProductSpaceReal`.
-/

public section

namespace MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted

/-- **Equal partial derivatives make a function constant on the lines `x + y = c`.**
Let `E` be a real normed space. If `f : ℝ × ℝ → E` is
differentiable and its partial derivatives agree, `∂₁f = ∂₂f` on `ℝ × ℝ`, then
`f (x, y) = f (x + y, 0)` for all `x, y : ℝ`. -/
theorem apply_eq_apply_add_zero_of_fderiv_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ × ℝ → E} (hf : Differentiable ℝ f)
    (hpar : ∀ p : ℝ × ℝ, (fderiv ℝ f p) (1, 0) = (fderiv ℝ f p) (0, 1)) (x y : ℝ) :
    f (x, y) = f (x + y, 0) := by
  -- The derivative of `t ↦ f (x + t, y - t)` is `∂₁f - ∂₂f = 0`.
  have hderiv (t : ℝ) : HasDerivAt (fun t => f (x + t, y - t)) 0 t := by
    have hline : HasDerivAt (fun t : ℝ => (x + t, y - t)) ((1 : ℝ), (-1 : ℝ)) t :=
      ((hasDerivAt_id t).const_add x).prodMk ((hasDerivAt_id t).const_sub y)
    have h := (hf (x + t, y - t)).hasFDerivAt.comp_hasDerivAt t hline
    rwa [show ((1 : ℝ), (-1 : ℝ)) = (1, 0) - (0, 1) by simp, map_sub, hpar, sub_self] at h
  simpa using is_const_of_deriv_eq_zero (fun t => (hderiv t).differentiableAt)
    (fun t => (hderiv t).deriv) 0 y

/-- **Equal partial derivatives give a factor `x + y`, for a differentiable function.** Let
`f : ℝ × ℝ → ℝ` be differentiable with `∂₁f = ∂₂f` on `ℝ × ℝ` and `f (0, 0) = 0`. Then there is a
continuous `g : ℝ × ℝ → ℝ` with `f (x, y) = g (x, y) * (x + y)` for all `x, y : ℝ`. -/
theorem exists_continuous_mul_add_of_differentiable {f : ℝ × ℝ → ℝ} (hf : Differentiable ℝ f)
    (hpar : ∀ p : ℝ × ℝ, (fderiv ℝ f p) (1, 0) = (fderiv ℝ f p) (0, 1))
    (h0 : f (0, 0) = 0) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧
      ∀ x y : ℝ, f (x, y) = g (x, y) * (x + y) := by
  set h : ℝ → ℝ := fun t => f (t, 0) with h_def
  have hh : Differentiable ℝ h := hf.comp (differentiable_id.prodMk (differentiable_const 0))
  refine ⟨fun p => dslope h 0 (p.1 + p.2), ?_, fun x y => ?_⟩
  · have hcont : Continuous (dslope h 0) := by
      rw [← continuousOn_univ, continuousOn_dslope Filter.univ_mem]
      exact ⟨hh.continuous.continuousOn, hh 0⟩
    exact hcont.comp (continuous_fst.add continuous_snd)
  · have hslope := sub_smul_dslope h 0 (x + y)
    simp only [sub_zero, smul_eq_mul, h_def, h0] at hslope
    rw [apply_eq_apply_add_zero_of_fderiv_eq hf hpar, mul_comm, hslope]

/-- **Equal partial derivatives give a factor $x+y$.** Let $f : \mathbb{R}^2 \to \mathbb{R}$ be
continuously differentiable with $\partial_1 f = \partial_2 f$ on $\mathbb{R}^2$ and $f(0,0)=0$.
Then there is a continuous $g : \mathbb{R}^2 \to \mathbb{R}$ with $f(x,y)=g(x,y)\,(x+y)$ for all
$(x,y)\in\mathbb{R}^2$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_02.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_continuous_mul_add_of_fderiv_eq {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hpar : ∀ p : ℝ × ℝ, (fderiv ℝ f p) (1, 0) = (fderiv ℝ f p) (0, 1))
    (h0 : f (0, 0) = 0) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧
      ∀ x y : ℝ, f (x, y) = g (x, y) * (x + y) :=
  exists_continuous_mul_add_of_differentiable (hf.differentiable one_ne_zero) hpar h0

end MathlibExt.Analysis.Calculus.EqualPartialsFactorSumWanted
