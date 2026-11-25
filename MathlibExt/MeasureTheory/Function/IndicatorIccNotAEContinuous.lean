/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# The indicator of [0,1] is not a.e. equal to a continuous function

The following OpenBMB notice applies to the adapted statement and its documentation.

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_28.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_28 … := by sorry` into the Batteries `theorem_wanted`
`not_exists_continuous_ae_eq_indicator_Icc`; moved the informal problem statement docstring onto
it and placed the declarations in namespace
`MathlibExt.MeasureTheory.IndicatorIccNotAEContinuousWanted`; replaced `import Mathlib` by
`public import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the module used.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # The unit-interval indicator has no continuous representative -/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.MeasureTheory.IndicatorIccNotAEContinuousWanted

/-- **No continuous function agrees a.e. with the indicator of $[0,1]$.** Let $\chi_{[0,1]}$ be
the characteristic function of $[0,1]$. There is no continuous function
$f : \mathbb{R} \to \mathbb{R}$ such that $f(x) = \chi_{[0,1]}(x)$ for almost every
$x \in \mathbb{R}$ with respect to Lebesgue measure.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Measure and integration;
Classical measure theory), `benchmark/level1/ma_proofbench_l1_28.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem not_exists_continuous_ae_eq_indicator_Icc : ¬ ∃ f : ℝ → ℝ, Continuous f ∧
    (∀ᵐ x ∂(MeasureTheory.volume),
      f x = Set.indicator (Set.Icc (0 : ℝ) 1) (fun _ => (1 : ℝ)) x) := by
  rintro ⟨f, hf, hae⟩
  let g := (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))
  have hnull : volume {x | f x ≠ g x} = 0 := ae_iff.mp hae
  -- Any disagreement on an open region where the indicator is constant would be open and null.
  have hconst (U : Set ℝ) (hU : IsOpen U) (c : ℝ) (hg : EqOn g (fun _ => c) U) :
      U ⊆ {x | f x = c} := by
    let V := U ∩ {x | f x ≠ c}
    have hV : IsOpen V := hU.inter (isOpen_ne.preimage hf)
    have hsub : V ⊆ {x | f x ≠ g x} := by
      intro x hx hfg
      exact hx.2 (hfg.trans (hg hx.1))
    have hVnull : volume V = 0 := measure_mono_null hsub hnull
    intro x hx
    by_contra hne
    have hxV : x ∈ V := ⟨hx, hne⟩
    rw [hV.eq_empty_of_measure_zero hVnull] at hxV
    exact hxV
  have hleft : Iio (0 : ℝ) ⊆ {x | f x = 0} := by
    refine hconst _ isOpen_Iio 0 ?_
    intro x hx
    exact indicator_of_notMem (fun hx' : x ∈ Icc (0 : ℝ) 1 => hx.not_ge hx'.1) _
  have hright : Ioo (0 : ℝ) 1 ⊆ {x | f x = 1} := by
    refine hconst _ isOpen_Ioo 1 ?_
    intro x hx
    exact indicator_of_mem (Ioo_subset_Icc_self hx) _
  have h₀ : f 0 = 0 := (isClosed_eq hf continuous_const).closure_subset_iff.mpr hleft <| by
    rw [closure_Iio]
    exact le_rfl
  have h₁ : f 0 = 1 := (isClosed_eq hf continuous_const).closure_subset_iff.mpr hright <| by
    rw [closure_Ioo zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  exact zero_ne_one (h₀.symm.trans h₁)

end MathlibExt.MeasureTheory.IndicatorIccNotAEContinuousWanted
