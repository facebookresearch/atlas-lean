/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_44.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the statement of Cauchy's formula.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li,
Jie Zhou and Yudong Wang (MA-ProofBench)
Licensed under the MIT License.

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
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Cauchy's formula for the twice-iterated integral

Integrate by parts with the weight `t ↦ s - t` and the primitive `t ↦ ∫ τ in α..t, f τ`.
The weight vanishes at the upper endpoint and the primitive vanishes at the lower endpoint.
-/

open Set MeasureTheory intervalIntegral

namespace MathlibExt.Analysis.Calculus.IteratedIntegralCauchyFormulaWanted

/-- **Cauchy's formula for the twice-iterated integral.** Let $E$ be a real Banach space, let
$\alpha \le \beta$ be real numbers and let $f : \mathbb{R} \to E$ be continuous on
$[\alpha, \beta]$. Then for every $s \in [\alpha, \beta]$,

$$\int_\alpha^s \Bigl(\int_\alpha^t f(\tau)\,d\tau\Bigr)\,dt = \int_\alpha^s (s - t)\, f(t)\,dt.$$

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_44.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem intervalIntegral_intervalIntegral_eq_integral_sub_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {α β : ℝ} (hαβ : α ≤ β) (f : ℝ → E) (hf : ContinuousOn f (Set.Icc α β)) :
    ∀ s ∈ Set.Icc α β,
      (∫ t in α..s, (∫ τ in α..t, f τ))
        = (∫ t in α..s, (s - t) • f t) := by
  intro s hs
  have hcont : ContinuousOn f (uIcc α s) := hf.mono (uIcc_subset_Icc ⟨le_rfl, hαβ⟩ hs)
  have hprim (x : ℝ) (hx : x ∈ uIcc α s) :
      HasDerivWithinAt (fun t => ∫ τ in α..t, f τ) (f x) (uIcc α s) x := by
    have : Fact (x ∈ uIcc α s) := ⟨hx⟩
    exact integral_hasDerivWithinAt_right (hcont.intervalIntegrable.mono_set
      (uIcc_subset_uIcc_left hx))
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_uIcc x) (hcont x hx)
  simpa using (integral_smul_deriv_eq_deriv_smul_of_hasDerivWithinAt
    (u' := fun _ => (-1 : ℝ)) (fun x _ => ((hasDerivAt_id x).const_sub s).hasDerivWithinAt)
    hprim intervalIntegrable_const hcont.intervalIntegrable).symm

end MathlibExt.Analysis.Calculus.IteratedIntegralCauchyFormulaWanted
