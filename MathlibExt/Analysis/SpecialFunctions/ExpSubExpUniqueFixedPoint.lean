/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_59.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the theorem statement.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu,
Xin Li, Jie Zhou, Yudong Wang.
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

public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The unique fixed point of a difference of exponentials

Writing `t = x - 1` turns the fixed-point equation into `sinh t + (sinh t - t) = 1`.
Both summands are strictly increasing, and their sum takes values on either side of
`1` at `t = 0` and `t = 1`.
-/

namespace MathlibExt.Analysis.SpecialFunctions.ExpSubExpUniqueFixedPointWanted

/-- **The map $x \mapsto e^{x-1} - e^{1-x}$ has a unique fixed point.** There is exactly one
real number $x$ such that $e^{x-1} - e^{1-x} = x$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_59.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem existsUnique_exp_sub_one_sub_exp_one_sub_eq_self :
    ∃! x : ℝ, (Real.exp (x - 1) - Real.exp (1 - x)) = x := by
  let f (t : ℝ) := Real.sinh t + (Real.sinh t - t)
  have hmono : StrictMono f := Real.sinh_strictMono.add Real.sinh_sub_id_strictMono
  have hcont : Continuous f := Real.continuous_sinh.add (Real.continuous_sinh.sub continuous_id)
  have hlevel : (1 : ℝ) ∈ Set.Icc (f 0) (f 1) := by
    constructor
    · simp [f]
    · dsimp [f]
      linarith [Real.self_le_sinh_iff.mpr (zero_le_one : (0 : ℝ) ≤ 1)]
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont.continuousOn hlevel
  have hfixed (x : ℝ) : Real.exp (x - 1) - Real.exp (1 - x) = x ↔ f (x - 1) = 1 := by
    simp only [f, Real.sinh_eq, neg_sub]
    constructor <;> intro h <;> linarith
  refine ⟨t + 1, (hfixed _).2 (by simpa using ht), ?_⟩
  intro y hy
  have := hmono.injective (((hfixed y).1 hy).trans ht.symm)
  linarith

end MathlibExt.Analysis.SpecialFunctions.ExpSubExpUniqueFixedPointWanted
