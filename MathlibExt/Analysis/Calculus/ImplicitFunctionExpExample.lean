/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_43.lean` (openbmb/ma-proofbench, commit 31bab4c):
Copyright (c) 2026 OpenBMB
Licensed under the MIT License.
Authors: Lushi Pu et al.

The theorem statement is adapted from this source.

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

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# An implicit function for a polynomial-exponential equation

At the root `(x, y₁, y₂) = (0, 1, -1)`, the partial derivative in `x` is the identity.
The implicit function theorem therefore gives a differentiable solution for `x` near `(1, -1)`.
-/

public section

namespace MathlibExt.Analysis.Calculus.ImplicitFunctionExpExampleWanted

open scoped Topology
open Filter

/-- **An implicit function for $x^2y_1+e^x+y_2=0$ near $(1,-1)$.** Let
$f(x,y_1,y_2)=x^2y_1+e^x+y_2$ on $\mathbb{R}^3$. Then there are an open set
$U\subseteq\mathbb{R}^2$ containing $(1,-1)$ and a function $g : \mathbb{R}^2 \to \mathbb{R}$,
differentiable on $U$, with $g(1,-1)=0$ and $f(g(y_1,y_2),y_1,y_2)=0$ for all $(y_1,y_2)\in U$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
several variables), `benchmark/level1/ma_proofbench_l1_43.lean` at
openbmb/ma-proofbench@31bab4c.
-/
theorem exists_implicit_function_sq_mul_add_exp_add
    (f : ℝ → ℝ → ℝ → ℝ) (hf : f = fun x y₁ y₂ => x ^ 2 * y₁ + Real.exp x + y₂) :
    ∃ (U : Set (ℝ × ℝ)), IsOpen U ∧ ((1, -1) ∈ U) ∧
      ∃ g : (ℝ × ℝ) → ℝ,
        DifferentiableOn ℝ g U ∧ g (1, -1) = 0 ∧ ∀ y ∈ U, f (g y) y.1 y.2 = 0 := by
  subst f
  let F : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 ^ 2 * p.1.1 + Real.exp p.2 + p.1.2
  let a : ℝ × ℝ := (1, -1)
  have hF : ContDiffAt ℝ 1 F (a, 0) := by
    dsimp [F]
    fun_prop
  have hx : HasDerivAt (fun x : ℝ => F (a, x)) 1 0 := by
    simpa [F, a] using
      (((hasDerivAt_pow 2 (0 : ℝ)).add (Real.hasDerivAt_exp 0)).add_const (-1))
  have hInv : (fderiv ℝ F (a, 0) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.refl ℝ ℝ, ?_⟩
    exact (hasFDerivAt_iff_hasDerivAt.mpr hx).unique
      ((hF.differentiableAt (by simp)).hasFDerivAt.comp 0 (hasFDerivAt_prodMk_right a 0))
  let g := hF.implicitFunction (by simp) hInv
  have hg : ContDiffAt ℝ 1 g a := hF.contDiffAt_implicitFunction (by simp) hInv
  have hroot : ∀ᶠ y in 𝓝 a, F (y, g y) = 0 := by
    simpa [F, a, g] using hF.eventually_apply_implicitFunction (by simp) hInv
  obtain ⟨U, hU, hopen, ha⟩ :=
    eventually_nhds_iff.mp ((hg.eventually (by simp)).and hroot)
  refine ⟨U, hopen, ha, g, ?_, hF.implicitFunction_apply_self (by simp) hInv,
    fun y hy => (hU y hy).2⟩
  exact fun y hy => ((hU y hy).1.differentiableAt (by simp)).differentiableWithinAt

end MathlibExt.Analysis.Calculus.ImplicitFunctionExpExampleWanted
