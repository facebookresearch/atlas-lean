/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.OrderClosed
import Code.OSSS.SharpnessFK

open scoped BigOperators
open Real Set

set_option linter.style.longLine false

namespace StatMech
namespace Walls














theorem osd_gronwall_lower (a b lam : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
    Real.exp (lam * (b - a)) * f a ≤ f b := by
  
  
  set h : ℝ → ℝ := fun x => f x * Real.exp (-lam * x) with hh
  have hderiv : ∀ x ∈ Icc a b,
      HasDerivAt h ((f' x - lam * f x) * Real.exp (-lam * x)) x := by
    intro x hx
    have hlin : HasDerivAt (fun y : ℝ => -lam * y) (-lam) x := by
      simpa using (hasDerivAt_id x).const_mul (-lam)
    have h1 : HasDerivAt (fun y => Real.exp (-lam * y)) (Real.exp (-lam * x) * (-lam)) x :=
      (Real.hasDerivAt_exp (-lam * x)).comp x hlin
    have hp := (hd x hx).mul h1
    convert hp using 1; ring
  
  have hmono : MonotoneOn h (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
    · exact fun x hx => (hderiv x (by simpa using hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x (mem_Icc_of_Ioo hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x (mem_Icc_of_Ioo hx)).deriv]
      apply mul_nonneg
      · have := hineq x (mem_Icc_of_Ioo hx); linarith
      · exact (Real.exp_pos _).le
  
  have hle := hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab
  rw [hh] at hle
  simp only [] at hle
  have hmul := mul_le_mul_of_nonneg_right hle (Real.exp_pos (lam * b)).le
  have e1 : Real.exp (-lam * a) * Real.exp (lam * b) = Real.exp (lam * (b - a)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-lam * b) * Real.exp (lam * b) = 1 := by
    rw [← Real.exp_add, show -lam * b + lam * b = 0 by ring, Real.exp_zero]
  have lhs : f a * Real.exp (-lam * a) * Real.exp (lam * b)
      = Real.exp (lam * (b - a)) * f a := by rw [mul_assoc, e1]; ring
  have rhs : f b * Real.exp (-lam * b) * Real.exp (lam * b) = f b := by
    rw [mul_assoc, e2, mul_one]
  rw [lhs, rhs] at hmul
  exact hmul









theorem osd_gronwall_decay (a b lam M : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x)
    (hfb : f b ≤ M) :
    f a ≤ M * Real.exp (-(lam * (b - a))) := by
  have hg := osd_gronwall_lower a b lam hab f f' hd hineq
  have hpos := Real.exp_pos (lam * (b - a))
  have h1 : Real.exp (lam * (b - a)) * f a ≤ M := hg.trans hfb
  rw [Real.exp_neg, le_mul_inv_iff₀ hpos]; linarith [h1]





theorem osd_gronwall_lower_eq_osss (a b lam : ℝ) (hab : a ≤ b) (f f' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
    osd_gronwall_lower a b lam hab f f' hd hineq
      = StatMech.OSSS.SharpnessFK.gronwall_lower a b lam hab f f' hd hineq :=
  rfl

end Walls
end StatMech
