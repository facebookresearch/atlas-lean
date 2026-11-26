/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Author: @toskua -/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Normed.Group.Indicator
public import Mathlib.Topology.Algebra.Indicator
public import Mathlib.Order.Filter.Defs

/-!
# Smooth zero extensions of real polynomials

Let l,r be arbitrary real numbers, P a real polynomial, and k ∈ ℕ. If
(X-l)^(k+1) (X-r)^(k+1) divides P, the function equal to P(x) on [l,r]
and zero outside that closed interval is C^k on ℝ, including both endpoints.
For r<l the interval is empty; for r=l the endpoint vanishing makes the extension zero.
-/

@[expose] public section

open Set Filter Asymptotics
open scoped Topology

namespace Polynomial

/-- For any set s ⊆ ℝ, real polynomial P and c : ℝ with P(c) = P'(c) = 0,
the function equal to P on s and zero off s has derivative zero at c. -/
private theorem hasDerivAt_indicator_zero (s : Set ℝ) (P : Polynomial ℝ) (c : ℝ)
    (h0 : P.eval c = 0) (h1 : P.derivative.eval c = 0) :
    HasDerivAt (s.indicator (fun x => P.eval x)) 0 c := by
  have hp := P.hasDerivAt c
  rw [h1] at hp
  have ho : (fun x => P.eval x) =o[𝓝 c] (fun x => x-c) := by
    simpa [h0] using hp.isLittleO
  have hf0 : s.indicator (fun x => P.eval x) c = 0 := by simp [h0]
  apply HasDerivAt.of_isLittleO
  simp only [hf0, sub_zero, smul_zero]
  apply IsLittleO.of_bound
  intro C hC
  filter_upwards [ho.bound hC] with x hx
  exact (norm_indicator_le_norm_self (s := s) (fun x => P.eval x) x).trans hx

/-- Let l,r be arbitrary real numbers and P a real polynomial with P(l) = P(r) = 0.
The function equal to P on [l,r] and zero outside it is continuous on ℝ. -/
private theorem continuous_indicator_Icc (l r : ℝ) (P : Polynomial ℝ)
    (h0 : P.eval l = 0) (h1 : P.eval r = 0) :
    Continuous ((Icc l r).indicator (fun x => P.eval x)) := by
  by_cases hlr : l ≤ r
  · apply P.differentiable.continuous.indicator
    intro x hx
    rw [frontier_Icc hlr] at hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact h0
    · exact h1
  · rw [Icc_eq_empty hlr]
    simp only [Set.indicator_empty]
    exact continuous_const

/-- For real l,r and a real polynomial P divisible by ((X-l)(X-r))², the derivative
of the function equal to P on [l,r] and zero outside it is P'(x) on [l,r]
and zero outside it, at every x : ℝ. -/
private theorem hasDerivAt_indicator_Icc (l r : ℝ) (P : Polynomial ℝ)
    (hP : ((X - C l) * (X - C r)) ^ 2 ∣ P) (x : ℝ) :
    HasDerivAt ((Icc l r).indicator (fun y => P.eval y))
      ((Icc l r).indicator (fun y => P.derivative.eval y) x) x := by
  have hd : (X - C l) * (X - C r) ∣ P.derivative := by
    simpa using pow_sub_one_dvd_derivative_of_pow_dvd hP
  have h0l : P.eval l = 0 := by obtain ⟨Q, hQ⟩ := hP; rw [hQ]; simp
  have h0r : P.eval r = 0 := by obtain ⟨Q, hQ⟩ := hP; rw [hQ]; simp
  have h1l : P.derivative.eval l = 0 := by obtain ⟨Q, hQ⟩ := hd; rw [hQ]; simp
  have h1r : P.derivative.eval r = 0 := by obtain ⟨Q, hQ⟩ := hd; rw [hQ]; simp
  by_cases hxl : x = l
  · subst x
    have hi : (Icc l r).indicator (fun y => P.derivative.eval y) l = 0 :=
      indicator_apply_eq_zero.mpr (fun _ => h1l)
    rw [hi]
    exact hasDerivAt_indicator_zero (Icc l r) P l h0l h1l
  by_cases hxr : x = r
  · subst x
    have hi : (Icc l r).indicator (fun y => P.derivative.eval y) r = 0 :=
      indicator_apply_eq_zero.mpr (fun _ => h1r)
    rw [hi]
    exact hasDerivAt_indicator_zero (Icc l r) P r h0r h1r
  by_cases hx : x ∈ Icc l r
  · have hxo : x ∈ Ioo l r :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
    have heq : (Icc l r).indicator (fun y => P.eval y) =ᶠ[𝓝 x] (fun y => P.eval y) := by
      filter_upwards [isOpen_Ioo.mem_nhds hxo] with y hy
      exact indicator_of_mem (s := Icc l r) (a := y) ⟨hy.1.le, hy.2.le⟩ (fun z => P.eval z)
    rw [indicator_of_mem hx]
    exact (P.hasDerivAt x).congr_of_eventuallyEq heq
  · have heq : (Icc l r).indicator (fun y => P.eval y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
      exact indicator_of_notMem hy _
    rw [indicator_of_notMem hx]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq

/-- Let l,r be arbitrary real numbers, P a real polynomial and k ∈ ℕ.
If (X-l)^(k+1) (X-r)^(k+1) divides P, its closed-interval zero extension
is C^k on ℝ, including through order k at both endpoints. Empty and degenerate
intervals give the zero function and are included. -/
theorem contDiff_indicator_Icc_of_factor (l r : ℝ) (P : Polynomial ℝ) (k : ℕ)
    (hP : (X - C l) ^ (k + 1) * (X - C r) ^ (k + 1) ∣ P) :
    ContDiff ℝ (k : WithTop ℕ∞) ((Icc l r).indicator (fun x => P.eval x)) := by
  have hpow : ((X - C l) * (X - C r)) ^ (k + 1) ∣ P := by simpa only [mul_pow] using hP
  clear hP
  induction k generalizing P with
  | zero =>
    apply contDiff_zero.mpr
    have h0 : P.eval l = 0 := by obtain ⟨Q, hQ⟩ := hpow; rw [hQ]; simp
    have h1 : P.eval r = 0 := by obtain ⟨Q, hQ⟩ := hpow; rw [hQ]; simp
    exact continuous_indicator_Icc l r P h0 h1
  | succ k ih =>
    have hd : ((X - C l) * (X - C r)) ^ (k + 1) ∣ P.derivative := by
      simpa using pow_sub_one_dvd_derivative_of_pow_dvd hpow
    have h2 : ((X - C l) * (X - C r)) ^ 2 ∣ P :=
      (pow_dvd_pow _ (by omega : 2 ≤ k + 1 + 1)).trans hpow
    have hder := hasDerivAt_indicator_Icc l r P h2
    have heq : deriv ((Icc l r).indicator (fun x => P.eval x)) =
        (Icc l r).indicator (fun x => P.derivative.eval x) := by
      funext x
      exact (hder x).deriv
    rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_deriv]
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · intro hk
      simp at hk
    · rw [heq]
      exact ih P.derivative hd

end Polynomial
