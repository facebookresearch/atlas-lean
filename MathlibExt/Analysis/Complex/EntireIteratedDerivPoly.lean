/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_90.lean` (openbmb/ma-proofbench, commit 31bab4c).
Authors: Lushi Pu, Weiming Zhang, Xinheng Xie, Zixuan Fu, Bingxiang He, Hongya Lyu,
Xin Li, Jie Zhou, Yudong Wang.
The theorem statement is adapted from this source under the MIT License.

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

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Entire functions with polynomial iterated derivatives

A polynomial has a polynomial primitive, and two entire functions with the same derivative
differ by a constant. Iterating this observation recovers the function from its polynomial
derivative up to the constants of integration.
-/

public section

namespace MathlibExt.Analysis.Complex.EntireIteratedDerivPolyWanted

private theorem exists_primitive (p : Polynomial ℂ) :
    ∃ q : Polynomial ℂ, q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', by rw [Polynomial.derivative_add, hp', hq']⟩
  | monomial n a =>
    refine ⟨Polynomial.monomial (n + 1) (a / (n + 1)), ?_⟩
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [hn]

private theorem exists_polynomial_of_deriv_eq_polynomial {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h : ∃ p : Polynomial ℂ, deriv f = fun z => p.eval z) :
    ∃ q : Polynomial ℂ, f = fun z => q.eval z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := exists_primitive p
  obtain ⟨c, hc⟩ := isOpen_univ.exists_eq_add_of_deriv_eq isPreconnected_univ
    hf.differentiableOn q.differentiable.differentiableOn
    (fun z _ => by rw [Polynomial.deriv, hq, hp])
  exact ⟨q + Polynomial.C c, funext fun z => by simpa using hc (Set.mem_univ z)⟩

/-- **An entire function with a polynomial derivative is a polynomial.** Let $k$ be a positive
integer and let $f : \mathbb{C} \to \mathbb{C}$ be an entire function. If there is a complex
polynomial $p$ such that the $k$th derivative of $f$ satisfies $f^{(k)}(z) = p(z)$ for all
$z \in \mathbb{C}$, then there is a complex polynomial $q$ such that $f(z) = q(z)$ for all
$z \in \mathbb{C}$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Functions of a complex
variable; Entire and meromorphic functions of one complex variable, and related topics),
`benchmark/level1/ma_proofbench_l1_90.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem exists_polynomial_of_iteratedDeriv_eq_polynomial
    {k : ℕ} (hk : 0 < k) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hpoly : ∃ p : Polynomial ℂ, iteratedDeriv k f = fun z => p.eval z) :
    ∃ q : Polynomial ℂ, f = fun z => q.eval z := by
  change 1 ≤ k at hk
  induction k, hk using Nat.le_induction generalizing f with
  | base =>
    rw [iteratedDeriv_one] at hpoly
    exact exists_polynomial_of_deriv_eq_polynomial hf hpoly
  | succ k _ ih =>
    rw [iteratedDeriv_succ'] at hpoly
    exact exists_polynomial_of_deriv_eq_polynomial hf (ih hf.deriv hpoly)

end MathlibExt.Analysis.Complex.EntireIteratedDerivPolyWanted
