/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Nonlinear feedback: local sign condition and quadratic energy decay

## i. Overview

For a scalar energy model `C*T' = F(T)` with an equilibrium `T*`
satisfying `F(T*) = 0`, if `F` is differentiable near `T*` and
`deriv F < 0` on a punctured neighbourhood of `T*` (the derivative at
`T*` itself may vanish, as for `F(T) = -(T - T*)^3`), then
`(T - T*) * F(T) < 0` for `T ≠ T*` nearby (mean value theorem).

Separately, for an arbitrary reference value `T*`, not assumed to be an
equilibrium, at a time where a solution satisfies `(T - T*) * F(T) < 0`
the quadratic energy `V = (T - T*)^2/2` has derivative
`V' = (T - T*) * F(T) / C < 0`. At an equilibrium, combined with the local
sign condition, this is the Lyapunov reading: `V' < 0` at every time the
solution lies in the punctured neighbourhood. This is a local,
model-conditional statement; a model bifurcation is not an empirical
climate threshold, and discontinuous albedo needs piecewise analysis.

## ii. Key results

- `EarthScience.local_sign`: negative derivative gives the local sign condition.
- `EarthScience.quadratic_energy_decay_about_reference`: pointwise decay of
  `(T - T*)^2/2` about an arbitrary reference value `T*`, given the model
  equation and the sign of `(T - T*) * F(T)` at one time.
- `EarthScience.linear_witness`: linear attracting model satisfies the sign condition.
- `EarthScience.unstable_witness`: linear repelling model violates it.

## iii. Table of contents

- A. Main results

## iv. References

- See the individual theorem docstrings.
-/

@[expose] public section

namespace EarthScience


open Set

/-- Local sign condition from a negative derivative: if `F(T*) = 0`,
`F` is differentiable on `(T* - δ, T* + δ)`, and `deriv F < 0` on the
punctured neighbourhood `(T* - δ, T* + δ) \ {T*}`, then
`(T - T*) * F(T) < 0` for `T ≠ T*` in it. Proved via the mean value
theorem, whose intermediate point differs from `T*`. -/
theorem local_sign {F : ℝ → ℝ} {Tstar δ : ℝ} (hδ : 0 < δ)
    (hF : F Tstar = 0)
    (hdiff : ∀ T ∈ Set.Ioo (Tstar - δ) (Tstar + δ), DifferentiableAt ℝ F T)
    (hneg : ∀ T ∈ Set.Ioo (Tstar - δ) (Tstar + δ), T ≠ Tstar → deriv F T < 0)
    {T : ℝ} (hT : T ∈ Set.Ioo (Tstar - δ) (Tstar + δ)) (hne : T ≠ Tstar) :
    (T - Tstar) * F T < 0 := by
  have hdiffOn : DifferentiableOn ℝ F (Set.Ioo (Tstar - δ) (Tstar + δ)) :=
    fun x hx => (hdiff x hx).differentiableWithinAt
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Case T < Tstar: use interval [T, Tstar]
    have hsubIcc : Set.Icc T Tstar ⊆ Set.Ioo (Tstar - δ) (Tstar + δ) := by
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ioo]
      constructor
      · linarith [hx.1, hT.1]
      · have h2 : Tstar < Tstar + δ := by linarith
        linarith [hx.2]
    have hsubIoo : Set.Ioo T Tstar ⊆ Set.Ioo (Tstar - δ) (Tstar + δ) := by
      intro x hx
      simp only [Set.mem_Ioo] at hx ⊢
      constructor
      · linarith [hx.1, hT.1]
      · have h2 : Tstar < Tstar + δ := by linarith
        linarith [hx.2]
    have hcont : ContinuousOn F (Set.Icc T Tstar) :=
      (hdiffOn.mono hsubIcc).continuousOn
    have hdiff' : DifferentiableOn ℝ F (Set.Ioo T Tstar) :=
      hdiffOn.mono hsubIoo
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope F hlt hcont hdiff'
    have hc_big : c ∈ Set.Ioo (Tstar - δ) (Tstar + δ) := hsubIoo hc_mem
    have hnegc : deriv F c < 0 := hneg c hc_big hc_mem.2.ne
    rw [hc_eq] at hnegc
    rw [hF] at hnegc
    have hdenom : 0 < Tstar - T := sub_pos.mpr hlt
    have hnum : 0 - F T < 0 := by
      rcases div_neg_iff.mp hnegc with ⟨_, hcon⟩ | ⟨hneg2, _⟩
      · linarith
      · exact hneg2
    have hFT : 0 < F T := by linarith
    have hdiff_neg : T - Tstar < 0 := sub_neg.mpr hlt
    exact mul_neg_of_neg_of_pos hdiff_neg hFT
  · -- Case Tstar < T: use interval [Tstar, T]
    have hsubIcc : Set.Icc Tstar T ⊆ Set.Ioo (Tstar - δ) (Tstar + δ) := by
      intro x hx
      simp only [Set.mem_Icc] at hx
      simp only [Set.mem_Ioo]
      constructor
      · have h1 : Tstar - δ < Tstar := by linarith
        linarith [hx.1]
      · linarith [hx.2, hT.2]
    have hsubIoo : Set.Ioo Tstar T ⊆ Set.Ioo (Tstar - δ) (Tstar + δ) := by
      intro x hx
      simp only [Set.mem_Ioo] at hx ⊢
      constructor
      · have h1 : Tstar - δ < Tstar := by linarith
        linarith [hx.1]
      · linarith [hx.2, hT.2]
    have hcont : ContinuousOn F (Set.Icc Tstar T) :=
      (hdiffOn.mono hsubIcc).continuousOn
    have hdiff' : DifferentiableOn ℝ F (Set.Ioo Tstar T) :=
      hdiffOn.mono hsubIoo
    obtain ⟨c, hc_mem, hc_eq⟩ := exists_deriv_eq_slope F hgt hcont hdiff'
    have hc_big : c ∈ Set.Ioo (Tstar - δ) (Tstar + δ) := hsubIoo hc_mem
    have hnegc : deriv F c < 0 := hneg c hc_big hc_mem.1.ne'
    rw [hc_eq] at hnegc
    rw [hF, sub_zero] at hnegc
    have hdenom : 0 < T - Tstar := sub_pos.mpr hgt
    have hFT : F T < 0 := by
      rcases div_neg_iff.mp hnegc with ⟨_, hcon⟩ | ⟨hneg2, _⟩
      · linarith
      · exact hneg2
    exact mul_neg_of_pos_of_neg hdenom hFT

/-- Pointwise quadratic-energy decay about an arbitrary reference value
`Tstar`: if `T` solves `C * T' = F(T)` at time `t` (stated as
`HasDerivAt T (F(T t)/C) t`) and `(T t - Tstar) * F(T t) < 0`, then the
energy `V(s) = (T s - Tstar)^2 / 2` has derivative
`(T t - Tstar) * F(T t) / C < 0` at `t`.

`Tstar` need not be an equilibrium and no neighbourhood sign condition is
assumed, so this alone says nothing about attraction. At an equilibrium
(`F Tstar = 0`) where `local_sign` supplies the sign hypothesis, it gives
the Lyapunov reading: `V` decreases at every time the solution lies in the
punctured neighbourhood. -/
theorem quadratic_energy_decay_about_reference {F : ℝ → ℝ} {C Tstar : ℝ} (hC : 0 < C)
    (T : ℝ → ℝ) (t : ℝ) (hne : T t ≠ Tstar)
    (hODE : HasDerivAt T (F (T t) / C) t)
    (hsign : (T t - Tstar) * F (T t) < 0) :
    HasDerivAt (fun t => (T t - Tstar) ^ 2 / 2) ((T t - Tstar) * F (T t) / C) t
    ∧ (T t - Tstar) * F (T t) / C < 0 := by
  have _ : T t ≠ Tstar := hne
  have hCne : C ≠ 0 := ne_of_gt hC
  have h1 : HasDerivAt (fun t => T t - Tstar) (F (T t) / C) t :=
    hODE.sub_const Tstar
  have h2 := h1.pow 2
  have h3 := h2.div_const (2 : ℝ)
  have heq : (↑(2 : ℕ) * (T t - Tstar) ^ (2 - 1) * (F (T t) / C) / 2)
      = ((T t - Tstar) * F (T t) / C) := by
    field_simp
    ring
  rw [heq] at h3
  refine ⟨h3, div_neg_of_neg_of_pos hsign hC⟩

/-- Linear model witness: for `F(T) = -k*(T - Tstar)` with `k > 0`,
the sign condition holds for every `T ≠ Tstar`. -/
theorem linear_witness {k Tstar T : ℝ} (hk : 0 < k) (hne : T ≠ Tstar) :
    (T - Tstar) * (-k * (T - Tstar)) < 0 := by
  have hd : T - Tstar ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (T - Tstar) ^ 2 := sq_pos_of_ne_zero hd
  have hpos : 0 < k * (T - Tstar) ^ 2 := mul_pos hk hsq
  have heq : (T - Tstar) * (-k * (T - Tstar)) = -(k * (T - Tstar) ^ 2) := by ring
  rw [heq]
  exact neg_lt_zero.mpr hpos

/-- Unstable branch witness: for `F(T) = k*(T - Tstar)` with `k > 0`,
the product is positive for `T ≠ Tstar` (repelling, not attracting). -/
theorem unstable_witness {k Tstar T : ℝ} (hk : 0 < k) (hne : T ≠ Tstar) :
    0 < (T - Tstar) * (k * (T - Tstar)) := by
  have hd : T - Tstar ≠ 0 := sub_ne_zero.mpr hne
  have hsq : 0 < (T - Tstar) ^ 2 := sq_pos_of_ne_zero hd
  have hpos : 0 < k * (T - Tstar) ^ 2 := mul_pos hk hsq
  have heq : (T - Tstar) * (k * (T - Tstar)) = k * (T - Tstar) ^ 2 := by ring
  rw [heq]
  exact hpos


end EarthScience
