/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_32.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029), for the theorem statement and its informal description.
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu, Xin Li,
Jie Zhou and Yudong Wang.
MIT License

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

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# Continuous real solutions of the exponential functional equation

A nonzero solution is everywhere positive. Its logarithm is a continuous additive map on
`ℝ`, so its value at one determines the exponent.
-/

public section

namespace MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExpWanted

/-- **Continuous nonzero solutions of $f(x)f(y) = f(x+y)$ are exponentials.** Let
$f : \mathbb{R} \to \mathbb{R}$ be a continuous function that is not identically zero and
satisfies $f(x)f(y) = f(x+y)$ for all real $x$ and $y$. Then there is a real constant $c$ such
that $f(x) = e^{cx}$ for every real $x$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_32.lean` at openbmb/ma-proofbench@31bab4c.
-/
theorem exists_eq_exp_mul_of_map_add_eq_mul
    {f : ℝ → ℝ}
    (hadd : ∀ x y : ℝ, f x * f y = f (x + y))
    (hcont : Continuous f)
    (hnz : f ≠ 0) :
    ∃ c : ℝ, ∀ x : ℝ, f x = Real.exp (c * x) := by
  have hne (x : ℝ) : f x ≠ 0 := by
    intro hx
    apply hnz
    funext y
    simpa [hx] using (hadd (y - x) x).symm
  have hpos (x : ℝ) : 0 < f x := by
    calc
      0 < f (x / 2) * f (x / 2) := mul_self_pos.mpr (hne _)
      _ = f x := by simpa using hadd (x / 2) (x / 2)
  let g : ℝ →+ ℝ := AddMonoidHom.mk' (fun x => Real.log (f x)) fun x y => by
    rw [← hadd, Real.log_mul (hne x) (hne y)]
  have hg : Continuous g := hcont.log hne
  refine ⟨g 1, fun x => ?_⟩
  have hx : g x = g 1 * x := by
    rw [mul_comm]
    simpa only [smul_eq_mul, mul_one] using map_real_smul g hg x 1
  calc
    f x = Real.exp (g x) := (Real.exp_log (hpos x)).symm
    _ = Real.exp (g 1 * x) := congrArg Real.exp hx

end MathlibExt.Analysis.SpecialFunctions.ContinuousMultiplicativeFunctionalEqExpWanted
