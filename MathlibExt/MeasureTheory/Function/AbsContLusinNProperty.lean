/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-
# Absolutely continuous functions map null sets to null sets

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
commit 31bab4c78fd1b0c464e767d62e9202163d1e9029, `benchmark/level1/ma_proofbench_l1_75.lean`
(MA-ProofBench, L. Pu et al., *MA-ProofBench: A Two-Tiered Evaluation of LLMs for Theorem
Proving in Mathematical Analysis*, arXiv:2606.13782), distributed under the MIT License above.
See also the Hugging Face dataset openbmb/MA-ProofBench. Changes made: converted
`theorem ma_proofbench_l1_75 … := by sorry` into the Batteries `theorem_wanted`
`volume_image_eq_zero_of_absolutelyContinuous`; moved the informal problem statement docstring
onto it and placed the declarations in namespace
`MathlibExt.MeasureTheory.AbsContLusinNPropertyWanted`; replaced `import Mathlib` by `public
import Mathlib` under the module system.
This move supplies a proof and narrows the imports to the modules used.
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # The Lusin N property for absolutely continuous real functions -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace MathlibExt.MeasureTheory.AbsContLusinNPropertyWanted

/-- **Absolutely continuous functions have the Lusin N property.** Let $f : \mathbb{R} \to
\mathbb{R}$ be absolutely continuous on every closed bounded interval $[a, b]$. Then $f$ maps
Lebesgue null sets to null sets: for every set $s \subseteq \mathbb{R}$ of Lebesgue outer measure
zero, the image $f(s)$ has Lebesgue outer measure zero.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_75.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem volume_image_eq_zero_of_absolutelyContinuous
    (f : ℝ → ℝ) (hf : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b) :
    ∀ s : Set ℝ, MeasureTheory.volume s = 0 → MeasureTheory.volume (f '' s) = 0 := by
  let g (b : ℝ) := ∫ x in (0 : ℝ)..b, ‖deriv f x‖
  have hint (a b : ℝ) : IntervalIntegrable (fun x => ‖deriv f x‖) volume a b :=
    (hf a b).intervalIntegrable_deriv.norm
  have hg_sub (a b : ℝ) : g b - g a = ∫ x in a..b, ‖deriv f x‖ :=
    intervalIntegral.integral_interval_sub_left (hint 0 b) (hint 0 a)
  have hg_mono : Monotone g := by
    intro a b hab
    exact sub_nonneg.mp ((hg_sub a b).trans_ge
      (intervalIntegral.integral_nonneg_of_forall hab fun _ => norm_nonneg _))
  have hg_cont : Continuous g := intervalIntegral.continuous_primitive hint _
  let G := hg_mono.stieltjesFunction
  have hG (a : ℝ) : G a = g a := by
    change hg_mono.stieltjesFunction a = g a
    rw [hg_mono.stieltjesFunction_eq]
    exact hg_cont.continuousAt.continuousWithinAt.rightLim_eq
  have hB : (inferInstance : MeasurableSpace ℝ) ≤ G.outer.caratheodory := by
    borelize ℝ
    exact G.borel_le_measurable
  let μ := G.outer.toMeasure hB
  have hμ : G.measure = μ := by
    apply Measure.ext_of_Ioc
    intro a b _
    change G.measure (Ioc a b) = G.outer.toMeasure hB (Ioc a b)
    rw [G.measure_Ioc, toMeasure_apply _ _ measurableSet_Ioc, G.outer_Ioc]
  -- The Stieltjes length is the integral of the derivative norm on each half-open interval.
  let ν := (volume : Measure ℝ).withDensity (fun x => ‖deriv f x‖ₑ)
  have hν : G.measure = ν := by
    apply Measure.ext_of_Ioc
    intro a b hab
    rw [StieltjesFunction.measure_Ioc, hG a, hG b, hg_sub, intervalIntegral.integral_of_le hab.le,
      withDensity_apply _ measurableSet_Ioc]
    exact ofReal_integral_norm_eq_lintegral_eNorm
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp (hf a b).intervalIntegrable_deriv)
  have hdist (x y : ℝ) (hxy : x ≤ y) : dist (f x) (f y) ≤ G y - G x := by
    rw [hG x, hG y, hg_sub, dist_comm, Real.dist_eq, ← Real.norm_eq_abs,
      ← (hf x y).integral_deriv_eq_sub]
    exact intervalIntegral.norm_integral_le_integral_norm hxy
  -- This outer measure is the volume of the image, even for a nonmeasurable input set.
  let V := OuterMeasure.comap f (volume : Measure ℝ).toOuterMeasure
  have hIoc (a b : ℝ) : V (Ioc a b) ≤ ENNReal.ofReal (G b - G a) := by
    change volume (f '' Ioc a b) ≤ _
    refine (Real.volume_le_diam _).trans (Metric.ediam_le_of_forall_dist_le ?_)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases le_total x y with hxy | hyx
    · exact (hdist x y hxy).trans (sub_le_sub (G.mono hy.2) (G.mono hx.1.le))
    · rw [dist_comm]
      exact (hdist y x hyx).trans (sub_le_sub (G.mono hx.2) (G.mono hy.1.le))
  have hV : V ≤ G.outer := by
    apply OuterMeasure.le_ofFunction.mpr
    intro t
    have hbot : (botSet : Set ℝ) = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr fun x => not_isBot x
    rw [G.length_eq, hbot, sdiff_empty]
    refine le_iInf fun a => le_iInf fun b => le_iInf fun ht => ?_
    exact (measure_mono ht).trans (hIoc a b)
  intro s hs
  have hνs : ν s = 0 := withDensity_absolutelyContinuous _ _ hs
  apply nonpos_iff_eq_zero.mp
  calc
    volume (f '' s) = V s := rfl
    _ ≤ G.outer s := hV s
    _ ≤ μ s := le_toMeasure_apply _ _ _
    _ = 0 := by rw [← hμ, hν, hνs]

end MathlibExt.MeasureTheory.AbsContLusinNPropertyWanted
