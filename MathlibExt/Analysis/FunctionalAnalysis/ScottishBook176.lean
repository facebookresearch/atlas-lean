/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval

/-!
# Eidelheit's example for Scottish Book Problem 176

We refute Eidelheit's claim in Scottish Book Problem 176 using composition by squaring on
real continuous functions on the unit interval.
-/

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted

/-- **Scottish Book Problem 176 (Eidelheit's claim).** The claim that in every complete normed
ring $A$ (so $\|xy\| \le \|x\| \, \|y\|$, and $A$ has a unit) that is a normed algebra over
$\mathbb{R}$, the inverse of every invertible element is a limit of real polynomials in that
element: whenever $a, b \in A$ satisfy $ab = 1$ and $ba = 1$, there is a sequence
$(p_n)_{n \ge 0}$ of real polynomials with $p_n(a) \to b$ as $n \to \infty$. -/
def ScottishBookProblem176Claim : Prop :=
  ∀ (A : Type) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a b : A), a * b = 1 → b * a = 1 →
    ∃ p : ℕ → Polynomial ℝ,
      Filter.Tendsto (fun n => Polynomial.aeval a (p n)) Filter.atTop (nhds b)

open scoped unitInterval

private theorem sq_le_self (x : I) : (x : ℝ) ^ 2 ≤ x := by
  simpa only [pow_two, mul_one] using
    mul_le_mul_of_nonneg_left (unitInterval.le_one x) (unitInterval.nonneg x)

private noncomputable def square : C(I, I) where
  toFun x := ⟨(x : ℝ) ^ 2, pow_nonneg (unitInterval.nonneg x) 2,
    (sq_le_self x).trans (unitInterval.le_one x)⟩
  continuous_toFun := (continuous_subtype_val.pow 2).subtype_mk _

private noncomputable def squareRoot : C(I, I) where
  toFun x := ⟨Real.sqrt x, Real.sqrt_nonneg _, by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (unitInterval.le_one x)⟩
  continuous_toFun := (Real.continuous_sqrt.comp continuous_subtype_val).subtype_mk _

/--
**Eidelheit's Problem 176 has a negative answer.** The claim of Scottish Book Problem 176 is
false: there are a complete normed ring $A$ that is a normed algebra over $\mathbb{R}$ and
elements $a, b \in A$ with $ab = 1$ and $ba = 1$ such that $b$ is not the limit of any sequence
$(p_n(a))_{n \ge 0}$ with $p_n$ real polynomials.

The counterexample recorded in the typescript is the ring of linear operations on the space
$C[0, 1]$, with $a$ the operation $U$ given by $U(x)(t) = x(t^2)$ for $0 \le t \le 1$.

Source: M. Eidelheit,
Problem 176 of the Scottish Book, with the negative answer recorded in
Ad 176 of the typescript (November 11, 1938). See the commentary in
R. D. Mauldin (ed.), The Scottish Book, 2nd ed. (Birkhäuser, 2015).
-/
theorem eidelheit176_refuted : ¬ ScottishBookProblem176Claim := by
  intro claim
  let U := ContinuousMap.compCLM ℝ ℝ square
  let V := ContinuousMap.compCLM ℝ ℝ squareRoot
  have hUV : U * V = 1 := by
    ext g x
    change g (squareRoot (square x)) = g x
    congr 1
    exact Subtype.ext (Real.sqrt_sq (unitInterval.nonneg x))
  have hVU : V * U = 1 := by
    ext g x
    change g (square (squareRoot x)) = g x
    congr 1
    exact Subtype.ext (Real.sq_sqrt (unitInterval.nonneg x))
  obtain ⟨p, hp⟩ := claim (C(I, ℝ) →L[ℝ] C(I, ℝ)) U V hUV hVU
  let t : I := ⟨1 / 4, by constructor <;> norm_num⟩
  let f : C(I, ℝ) := ⟨fun x => max 0 ((x : ℝ) - (t : ℝ)),
    continuous_const.max (continuous_subtype_val.sub continuous_const)⟩
  -- The interval below t is invariant under squaring, and f vanishes there.
  have hpow (n : ℕ) (x : I) (hx : (x : ℝ) ≤ t) : ((U ^ n) f) x = 0 := by
    induction n generalizing x with
    | zero =>
      rw [pow_zero, one_apply_eq_self]
      change max 0 ((x : ℝ) - (t : ℝ)) = 0
      exact max_eq_left (sub_nonpos.mpr hx)
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      change ((U ^ n) f) (square x) = 0
      exact ih (square x) ((sq_le_self x).trans hx)
  have hpoly (q : Polynomial ℝ) : ((Polynomial.aeval U q) f) t = 0 := by
    induction q using Polynomial.induction_on' with
    | add q r hq hr =>
      simp only [map_add, add_apply, ContinuousMap.add_apply, hq, hr, add_zero]
    | monomial n c =>
      simp only [Polynomial.aeval_monomial, mul_apply_eq_comp,
        ContinuousLinearMap.algebraMap_apply, ContinuousMap.smul_apply, hpow n t le_rfl, smul_zero]
  -- Applying an operator to f and evaluating at t is continuous in the operator norm.
  let eval := (ContinuousMap.evalCLM ℝ t).comp (ContinuousLinearMap.apply ℝ C(I, ℝ) f)
  have hlim : Filter.Tendsto (fun n => ((Polynomial.aeval U (p n)) f) t)
      Filter.atTop (nhds ((V f) t)) :=
    (eval.continuous.tendsto V).comp hp
  have hzero : (V f) t = 0 := tendsto_nhds_unique hlim (by
    simpa only [hpoly] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0)))
  change max 0 (Real.sqrt (1 / 4) - 1 / 4) = 0 at hzero
  have hsqrt : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt] at hzero
  norm_num at hzero

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook176Wanted
