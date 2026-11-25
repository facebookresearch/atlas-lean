/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`benchmark/level1/ma_proofbench_l1_51.lean` (openbmb/ma-proofbench, commit
31bab4c78fd1b0c464e767d62e9202163d1e9029): the theorem statement.
Authors: L. Pu et al. (MA-ProofBench).
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

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Vanishing moments on the unit interval

Integration against a continuous function vanishes on polynomials if all its moments vanish.
By Weierstrass approximation it then vanishes on every continuous function on the interval,
including the function itself.
-/

namespace MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZeroWanted

open Set
open scoped Polynomial unitInterval

private theorem integral_mul_eval_eq_zero {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1))
    (h : ∀ n : ℕ, (∫ x in 0..1, f x * x ^ n) = 0) (p : ℝ[X]) :
    (∫ x in 0..1, f x * p.eval x) = 0 := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
    simp only [Polynomial.eval_monomial, mul_left_comm (f _), intervalIntegral.integral_const_mul,
      h, mul_zero]
  | add p q hp hq =>
    simp only [Polynomial.eval_add, mul_add]
    rw [intervalIntegral.integral_add, hp, hq, add_zero]
    · exact (hf.mul p.continuous.continuousOn).intervalIntegrable_of_Icc zero_le_one
    · exact (hf.mul q.continuous.continuousOn).intervalIntegrable_of_Icc zero_le_one

/-- **A function continuous on $[0,1]$ with vanishing moments is zero on $[0,1]$.** Let
$f : \mathbb{R} \to \mathbb{R}$ be continuous on $[0,1]$, and suppose that
$\int_0^1 f(x)\,x^n\,dx = 0$ for every natural number $n = 0, 1, 2, \dots$. Then $f(x) = 0$ for
every $x \in [0,1]$.

Source: MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level I (Real functions; Functions of
one variable), `benchmark/level1/ma_proofbench_l1_51.lean` at openbmb/ma-proofbench@31bab4c.
-/
public theorem eqOn_zero_of_integral_mul_pow_eq_zero
    (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1))
    (h : ∀ n : ℕ, (∫ x in 0..1, f x * x ^ n) = 0) :
    Set.EqOn f 0 (Set.Icc 0 1) := by
  let F : C(I, ℝ) := ⟨_, continuousOn_iff_continuous_domRestrict.mp hf⟩
  -- Projecting onto the interval lets the interval integral evaluate bundled functions.
  let L (g : C(I, ℝ)) := ∫ x in (0 : ℝ)..1, (F * g) (projIcc 0 1 zero_le_one x)
  have hL : Continuous L := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous fun z : C(I, ℝ) × ℝ =>
      F (projIcc 0 1 zero_le_one z.2) * z.1 (projIcc 0 1 zero_le_one z.2)
    fun_prop
  have hrestrict (g : ℝ → ℝ) (hg : ContinuousOn g I) :
      L ⟨_, continuousOn_iff_continuous_domRestrict.mp hg⟩ = ∫ x in 0..1, f x * g x := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le zero_le_one]
    intro x hx
    simp [F, projIcc_of_mem _ hx]
  have hself : (∫ x in 0..1, f x * f x) = 0 := by
    rw [← hrestrict f hf]
    apply closure_minimal (s := (polynomialFunctions I : Set C(I, ℝ))) (t := {g | L g = 0})
      _ (isClosed_eq hL continuous_const)
      (continuousMap_mem_polynomialFunctions_closure 0 1 F)
    rw [polynomialFunctions_coe]
    rintro _ ⟨p, rfl⟩
    exact (hrestrict _ p.continuous.continuousOn).trans (integral_mul_eval_eq_zero hf h p)
  intro x hx
  by_contra hne
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    zero_lt_one (f := fun _ => 0) continuousOn_const (hf.mul hf)
    (fun y _ => mul_self_nonneg (f y)) ⟨x, hx, mul_self_pos.mpr hne⟩
  simp [hself] at hpos

end MathlibExt.Analysis.Calculus.VanishingMomentsImpliesZeroWanted
