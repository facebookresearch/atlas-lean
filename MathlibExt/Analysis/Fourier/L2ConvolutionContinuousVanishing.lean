/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
Portions of this file are adapted from:

`benchmark/level2/ma_proofbench_l2_17.lean` (openbmb/ma-proofbench at commit
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

Attribution and modification notice: the statement of
`continuous_and_tendsto_cocompact_convolution_of_memLp_two` below is taken from
openbmb/ma-proofbench at commit 31bab4c78fd1b0c464e767d62e9202163d1e9029,
`benchmark/level2/ma_proofbench_l2_17.lean` (MA-ProofBench, L. Pu et al., *MA-ProofBench: A
Two-Tiered Evaluation of LLMs for Theorem Proving in Mathematical Analysis*, arXiv:2606.13782;
byte-identical to the Hugging Face dataset openbmb/MA-ProofBench), distributed under the MIT
License above. Changes made: converted the benchmark theorem `ma_proofbench_l2_17`, whose proof
there is a placeholder, into the Batteries wanted-theorem declaration
`continuous_and_tendsto_cocompact_convolution_of_memLp_two` (a statement without a proof); moved
the informal problem statement docstring onto it and placed the declarations in namespace
`MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted`; replaced `import Mathlib`
by `public import Mathlib` under the module system. Further changes in this file: that wanted
declaration is now a `theorem` with a proof, and `public import Mathlib` is replaced by narrower
imports; the statement and its docstring are unchanged.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The convolution of two square-integrable functions is continuous and vanishes at infinity

For square-integrable `f g : (Fin n → ℝ) → ℂ`, the convolution `x ↦ ∫ y, f (x - y) * g y` is
continuous and tends to `0` along `Filter.cocompact`, that is, as `x` tends to infinity.

This function is Mathlib's convolution `f ⋆[ContinuousLinearMap.mul ℂ ℂ] g`
(`convolution_mul_swap`). By the Cauchy–Schwarz inequality and the invariance of Lebesgue measure
under translations and reflection, its norm is at most `‖f‖₂ ‖g‖₂` everywhere
(`eNorm_convolution_le`), and it is bilinear in `f` and `g`. Approximate `f` and `g` in `L²` by
continuous compactly supported `f'` and `g'` (`MemLp.exists_hasCompactSupport_eLpNorm_sub_le`):
the convolution of `f'` and `g'` is continuous and compactly supported, and the identity
`f ⋆ g - f' ⋆ g' = (f - f') ⋆ g + f' ⋆ (g - g')` bounds the difference by
`‖f - f'‖₂ ‖g‖₂ + ‖f'‖₂ ‖g - g'‖₂` everywhere. So `f ⋆ g` is a uniform limit of continuous
compactly supported functions, and such a limit is continuous and tends to `0` along `cocompact`.

## Main statements

* `continuous_and_tendsto_cocompact_convolution_of_memLp_two`: the statement above. This is the
  MA-ProofBench problem `ma_proofbench_l2_17`, formerly a `WantedExt` entry.

## Implementation notes

The statement needs the Bochner integral and Lebesgue measure on `ℝ`, which
`Mathlib.MeasureTheory.Measure.Haar.OfBasis` defines. `Mathlib.Analysis.CStarAlgebra.Classes` is
also imported publicly, so that the statement elaborates to the same term as under
`import Mathlib`, where it was first stated: the norm of `ℂ` is then found through
`instCommCStarAlgebraComplex`, as it is there.

## References

* L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem Proving in
  Mathematical Analysis*, arXiv:2606.13782, Level II, problem `ma_proofbench_l2_17`.
-/

@[expose] public section

open MeasureTheory Filter

namespace MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted

open scoped Convolution Topology

/-- A function that is a uniform limit of continuous compactly supported functions is continuous
and tends to `0` along `cocompact`. -/
private theorem continuous_and_tendsto_cocompact_of_forall_exists_norm_sub_le
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] {G : X → E}
    (h : ∀ ε > 0, ∃ H : X → E, Continuous H ∧ HasCompactSupport H ∧ ∀ x, ‖G x - H x‖ ≤ ε) :
    Continuous G ∧ Tendsto G (cocompact X) (𝓝 0) := by
  constructor
  · refine continuous_of_uniform_approx_of_continuous fun u hu ↦ ?_
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    obtain ⟨H, hHc, -, hH⟩ := h (ε / 2) (half_pos hε)
    refine ⟨H, hHc, fun x ↦ hεu ?_⟩
    rw [dist_eq_norm]
    exact (hH x).trans_lt (half_lt_self hε)
  · refine Metric.tendsto_nhds.2 fun ε hε ↦ ?_
    obtain ⟨H, -, hHs, hH⟩ := h (ε / 2) (half_pos hε)
    -- Outside the compact set `tsupport H`, `‖G x‖ = ‖G x - H x‖ ≤ ε / 2`.
    filter_upwards [hHs.isCompact.compl_mem_cocompact] with x hx
    have hx' := hH x
    rw [image_eq_zero_of_notMem_tsupport hx, sub_zero] at hx'
    rw [dist_zero_right]
    exact hx'.trans_lt (half_lt_self hε)

/-- The convolution of two square-integrable functions on `Fin n → ℝ` is uniformly approximated by
continuous compactly supported functions: by convolutions of continuous compactly supported
approximations of the two functions in `L²`. -/
private theorem exists_continuous_hasCompactSupport_norm_convolution_sub_le {n : ℕ}
    {f g : (Fin n → ℝ) → ℂ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ H : (Fin n → ℝ) → ℂ, Continuous H ∧ HasCompactSupport H ∧
      ∀ x, ‖(f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) x - H x‖ ≤ ε := by
  set L := ContinuousLinearMap.mul ℂ ℂ
  -- Cauchy–Schwarz: the convolution of `u` and `v` is bounded by `‖u‖₂ ‖v‖₂`, as `‖L‖ = 1`.
  have key {u v : (Fin n → ℝ) → ℂ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
      (x : Fin n → ℝ) : ‖(u ⋆[L] v) x‖ₑ ≤ eLpNorm u 2 volume * eLpNorm v 2 volume := by
    calc ‖(u ⋆[L] v) x‖ₑ ≤ ‖L‖ₑ * eLpNorm u 2 volume * eLpNorm v 2 volume :=
          eNorm_convolution_le L hu.aestronglyMeasurable hv.aestronglyMeasurable x
      _ = eLpNorm u 2 volume * eLpNorm v 2 volume := by
          rw [eNorm_eq_nnNorm, ContinuousLinearMap.opNNNorm_mul, ENNReal.coe_one, one_mul]
  have hε2 : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.2 (half_pos hε)).ne'
  -- Approximate `f` first, then `g` with an accuracy depending on the approximation of `f`.
  obtain ⟨f', hf's, hff', hf'c, hf'⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 2) / eLpNorm g 2 volume)
    (ENNReal.div_ne_zero.2 ⟨hε2, hg.eLpNorm_ne_top⟩)
  obtain ⟨g', hg's, hgg', hg'c, hg'⟩ := hg.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofNat_ne_top (ε := ENNReal.ofReal (ε / 2) / eLpNorm f' 2 volume)
    (ENNReal.div_ne_zero.2 ⟨hε2, hf'.eLpNorm_ne_top⟩)
  refine ⟨f' ⋆[L] g', hf's.continuous_convolution_left L hf'c hg'c.locallyIntegrable,
    hf's.convolution L hg's, fun x ↦ ?_⟩
  -- All four convolution integrals converge, by Hölder's inequality.
  have hdec : (f ⋆[L] g) x - (f' ⋆[L] g') x =
      ((f - f') ⋆[L] g) x + (f' ⋆[L] (g - g')) x := by
    simp only [convolution_def]
    rw [← integral_sub (ConvolutionExists.of_memLp_memLp L hf hg x)
        (ConvolutionExists.of_memLp_memLp L hf' hg' x),
      ← integral_add (ConvolutionExists.of_memLp_memLp L (hf.sub hf') hg x)
        (ConvolutionExists.of_memLp_memLp L hf' (hg.sub hg') x)]
    congr 1
    ext t
    simp only [L, Pi.sub_apply, ContinuousLinearMap.mul_apply']
    ring
  rw [← ENNReal.ofReal_le_ofReal_iff hε.le, ofReal_norm, hdec]
  calc ‖((f - f') ⋆[L] g) x + (f' ⋆[L] (g - g')) x‖ₑ
      ≤ ‖((f - f') ⋆[L] g) x‖ₑ + ‖(f' ⋆[L] (g - g')) x‖ₑ := eNorm_add_le _ _
    _ ≤ eLpNorm (f - f') 2 volume * eLpNorm g 2 volume +
        eLpNorm f' 2 volume * eLpNorm (g - g') 2 volume :=
          add_le_add (key (hf.sub hf') hg x) (key hf' (hg.sub hg') x)
    _ ≤ ENNReal.ofReal (ε / 2) / eLpNorm g 2 volume * eLpNorm g 2 volume +
        eLpNorm f' 2 volume * (ENNReal.ofReal (ε / 2) / eLpNorm f' 2 volume) := by
          gcongr
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add (by rw [mul_comm]; exact ENNReal.mul_div_le) ENNReal.mul_div_le
    _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- **Convolution of two square-integrable functions is continuous and vanishes at infinity.**
Let $n$ be a natural number and let $f, g : \mathbb{R}^n \to \mathbb{C}$ be square-integrable.
Then the convolution $(f \ast g)(x) = \int_{\mathbb{R}^n} f(x - y) \, g(y) \, dy$ is a continuous
function of $x \in \mathbb{R}^n$, and $(f \ast g)(x) \to 0$ as $|x| \to \infty$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear
function spaces and their duals), `benchmark/level2/ma_proofbench_l2_17.lean` at
openbmb/ma-proofbench@31bab4c.
-/
public theorem continuous_and_tendsto_cocompact_convolution_of_memLp_two
    (n : ℕ) (f g : (Fin n → ℝ) → ℂ)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Continuous (fun x : Fin n → ℝ => ∫ y, f (x - y) * g y) ∧
    Filter.Tendsto (fun x : Fin n → ℝ => ∫ y, f (x - y) * g y)
      (Filter.cocompact (Fin n → ℝ)) (nhds 0) := by
  -- The function is Mathlib's convolution of `f` and `g` for the multiplication of `ℂ`.
  have h : (fun x : Fin n → ℝ ↦ ∫ y, f (x - y) * g y) =
      f ⋆[ContinuousLinearMap.mul ℂ ℂ] g := by
    ext x
    exact convolution_mul_swap.symm
  rw [h]
  exact continuous_and_tendsto_cocompact_of_forall_exists_norm_sub_le fun ε hε ↦
    exists_continuous_hasCompactSupport_norm_convolution_sub_le hf hg hε

end MathlibExt.Analysis.Fourier.L2ConvolutionContinuousVanishingWanted
