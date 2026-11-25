/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import PhyslibExt.Instrumentation.DACLevelError
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Held DAC settling

## i. Overview

On one holding interval `[tk, tk1)` a digital-to-analog converter
holds a constant real level `u`, and a scalar first-order output
stage with time constant `tau > 0` obeys `tau * y' = u - y` at
every interior time, with `y` continuous on the whole closed
interval. The output is then the explicit settling output
`u + (y tk - u) * exp (-(t - tk) / tau)`, the value at the right
endpoint is the same formula at `tk1`, and the settling error
obeys `|y t - u| = |y tk - u| * exp (-(t - tk) / tau)`, so it
never exceeds the initial mismatch on the interval. A held level
may be the actual level `dacLevel Δ e k = Δ * k + e k` of an
integer code, from `PhyslibExt.Instrumentation.DACLevelError`;
composing the settling law with that level gives the settling
error relative to the code's actual level. A discontinuous
output reset or a time-varying input on the interval is outside
this model.

The proof of the explicit formula forms the integrating-factor
product `(y s - u) * exp ((s - tk) / tau)`. Its derivative is
zero on the open interval by the product rule and the equation
`tau * y' = u - y`, so the mean value theorem makes the product
constant on the closed interval; rearranging that constant
gives the formula, including at the right endpoint, where no
derivative is assumed.

## ii. Key results

- `heldOutput_eq_settlingOutput`: the explicit settling formula
  on one holding interval, at every time of the closed interval.
- `settlingError_eq`: the settling error is the initial
  mismatch times the exponential factor.
- `settling_correct`: the explicit formula, the endpoint
  recurrence, and the settling-error law together.
- `settlingOutput_at_start`, `heldOutput_endpoint_recurrence`
  and `settlingError_le_initial`: the value at the start of the
  interval, the endpoint value that starts the next interval,
  and the bound of the settling error by the initial mismatch.
- `heldOutput_twoIntervals` and `codeHeld_settlingError_eq`:
  the formula across a change of held level at a junction, and
  the settling error measured against the actual level of a
  code.

## iii. Table of contents

- A. The settling output
- B. One holding interval
- C. Two intervals and a code-held level

## iv. References

- D. Johns and K. Martin, *Analog Integrated Circuit Design*,
  2nd ed., Wiley, 2012: first-order settling of a stage driven
  by a held converter output, and the exponential approach of
  the output to its held value.

## A. The settling output

The explicit function `settlingOutput u yStart tk tau t`, and
its value at the start of the interval, where the elapsed time
is zero and the exponential factor is one.

## B. One holding interval

The explicit formula for a continuous output obeying
`tau * y' = u - y` inside one interval, the endpoint recurrence
at the right endpoint, the exact settling-error law, its bound
by the initial mismatch, and the three clauses together in
`settling_correct`.

## C. Two intervals and a code-held level

The second-interval formula when the held level changes at the
junction, with continuity across the junction and no derivative
assumed there, and the settling error measured against the
actual level `dacLevel Δ e k` of an integer code.
-/

@[expose] public section

open PhyslibExt.Instrumentation.DACLevelError

namespace PhyslibExt.Instrumentation.HeldDACSettling

/-- The explicit settling output on one holding interval: held
level plus initial mismatch decayed by the exponential factor. -/
noncomputable def settlingOutput (u yStart tk tau t : ℝ) : ℝ :=
  u + (yStart - u) * Real.exp (-(t - tk) / tau)

/-- The settling output at the start of the interval is the
initial output value, for every held level and time constant. -/
lemma settlingOutput_at_start (u yStart tk tau : ℝ) :
    settlingOutput u yStart tk tau tk = yStart := by
  simp [settlingOutput]

/-- Explicit formula on one holding interval: an output
continuous on the closed interval and obeying
`tau * y' = u - y` at every interior time equals the settling
output with its own initial value, at every time of the closed
interval including the right endpoint, for `tau > 0` and
`tk < tk1`. -/
theorem heldOutput_eq_settlingOutput (tau u tk tk1 : ℝ) (htau : 0 < tau)
    (htk : tk < tk1) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk1))
    (hdiff : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hode : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → tau * deriv y s = u - y s)
    (t : ℝ) (ht : t ∈ Set.Icc tk tk1) :
    y t = settlingOutput u (y tk) tk tau t := by
  have _htk_used : tk < tk1 := htk
  have htau_ne : tau ≠ 0 := ne_of_gt htau
  have hcont_sub : ContinuousOn (fun s => y s - u) (Set.Icc tk tk1) :=
    hcont.sub continuousOn_const
  have hcont_inner : ContinuousOn (fun s => (s - tk) / tau) (Set.Icc tk tk1) :=
    (continuousOn_id.sub continuousOn_const).div_const tau
  have hcont_E : ContinuousOn (fun s => Real.exp ((s - tk) / tau)) (Set.Icc tk tk1) :=
    Real.continuous_exp.comp_continuousOn hcont_inner
  have hcont_g : ContinuousOn (fun s => (y s - u) * Real.exp ((s - tk) / tau))
      (Set.Icc tk tk1) :=
    hcont_sub.mul hcont_E
  have hderiv_g : ∀ s ∈ Set.Ioo tk tk1,
      HasDerivAt (fun s => (y s - u) * Real.exp ((s - tk) / tau)) 0 s := by
    intro s hs
    have hode_s := hode s hs
    have h_y : HasDerivAt (fun s => y s - u) (deriv y s) s :=
      HasDerivAt.sub_const u (hdiff s hs).hasDerivAt
    have h_inner : HasDerivAt (fun s => (s - tk) / tau) (1 / tau) s :=
      (HasDerivAt.sub_const tk (hasDerivAt_id' s)).div_const tau
    have h_E : HasDerivAt (fun s => Real.exp ((s - tk) / tau))
        (Real.exp ((s - tk) / tau) * (1 / tau)) s :=
      h_inner.exp
    have h_prod : HasDerivAt (fun s => (y s - u) * Real.exp ((s - tk) / tau))
        (deriv y s * Real.exp ((s - tk) / tau) +
          (y s - u) * (Real.exp ((s - tk) / tau) * (1 / tau))) s :=
      h_y.mul h_E
    have h1 : deriv y s * tau + (y s - u) = 0 := by linear_combination hode_s
    have h2 : deriv y s * Real.exp ((s - tk) / tau) +
          (y s - u) * (Real.exp ((s - tk) / tau) * (1 / tau)) =
          Real.exp ((s - tk) / tau) * (deriv y s * tau + (y s - u)) / tau := by
      field_simp
    have hval : deriv y s * Real.exp ((s - tk) / tau) +
          (y s - u) * (Real.exp ((s - tk) / tau) * (1 / tau)) = 0 := by
      rw [h2, h1, mul_zero, zero_div]
    rw [hval] at h_prod
    exact h_prod
  have hgtk : (y t - u) * Real.exp ((t - tk) / tau) = y tk - u := by
    rcases lt_or_eq_of_le ht.1 with htk_t | h_eq
    · have hsub_cont : ContinuousOn
          (fun s => (y s - u) * Real.exp ((s - tk) / tau)) (Set.Icc tk t) :=
        hcont_g.mono (Set.Icc_subset_Icc le_rfl ht.2)
      have hsub_deriv : ∀ x ∈ Set.Ioo tk t,
          HasDerivAt (fun s => (y s - u) * Real.exp ((s - tk) / tau)) 0 x := by
        intro x hx
        exact hderiv_g x ⟨hx.1, lt_of_lt_of_le hx.2 ht.2⟩
      obtain ⟨c, hc_mem, hc⟩ := exists_hasDerivAt_eq_slope
        (fun s => (y s - u) * Real.exp ((s - tk) / tau)) (fun _ => 0)
        htk_t hsub_cont hsub_deriv
      simp at hc
      have hne : t - tk ≠ 0 := sub_ne_zero.mpr (ne_of_gt htk_t)
      have hc' : ((y t - u) * Real.exp ((t - tk) / tau) - (y tk - u)) / (t - tk) = 0 :=
        hc.symm
      rw [div_eq_zero_iff] at hc'
      rcases hc' with hzero | hcontra
      · exact sub_eq_zero.mp hzero
      · exact absurd hcontra hne
    · subst h_eq
      simp
  have hexp_mul : Real.exp ((t - tk) / tau) * Real.exp (-(t - tk) / tau) = 1 := by
    rw [← Real.exp_add]
    have harg : (t - tk) / tau + (-(t - tk) / tau) = 0 := by ring
    rw [harg, Real.exp_zero]
  have hmain : y t - u = (y tk - u) * Real.exp (-(t - tk) / tau) := by
    have h := congrArg (fun x => x * Real.exp (-(t - tk) / tau)) hgtk
    rw [mul_assoc, hexp_mul, mul_one] at h
    exact h
  unfold settlingOutput
  linarith

/-- Endpoint recurrence: under the same hypotheses, the output
at the right endpoint is the held level plus the initial
mismatch decayed over the whole interval length. This value is
the initial value of the next holding interval. -/
lemma heldOutput_endpoint_recurrence (tau u tk tk1 : ℝ) (htau : 0 < tau)
    (htk : tk < tk1) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk1))
    (hdiff : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hode : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → tau * deriv y s = u - y s) :
    y tk1 = u + (y tk - u) * Real.exp (-(tk1 - tk) / tau) := by
  have hmem : tk1 ∈ Set.Icc tk tk1 := ⟨le_of_lt htk, le_rfl⟩
  have h := heldOutput_eq_settlingOutput tau u tk tk1 htau htk y hcont hdiff hode tk1 hmem
  simpa [settlingOutput] using h

/-- Settling error on one holding interval: under the same
hypotheses, the absolute deviation from the held level is the
initial absolute deviation times the exponential factor, at
every time of the closed interval. -/
theorem settlingError_eq (tau u tk tk1 : ℝ) (htau : 0 < tau)
    (htk : tk < tk1) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk1))
    (hdiff : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hode : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → tau * deriv y s = u - y s)
    (t : ℝ) (ht : t ∈ Set.Icc tk tk1) :
    |y t - u| = |y tk - u| * Real.exp (-(t - tk) / tau) := by
  have h := heldOutput_eq_settlingOutput tau u tk tk1 htau htk y hcont hdiff hode t ht
  have hsub : y t - u = (y tk - u) * Real.exp (-(t - tk) / tau) := by
    rw [h]
    unfold settlingOutput
    ring
  rw [hsub, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- The settling error never exceeds the initial mismatch on
the interval, because the exponential factor is at most one
for nonnegative elapsed time, under the same hypotheses. -/
lemma settlingError_le_initial (tau u tk tk1 : ℝ) (htau : 0 < tau)
    (htk : tk < tk1) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk1))
    (hdiff : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hode : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → tau * deriv y s = u - y s)
    (t : ℝ) (ht : t ∈ Set.Icc tk tk1) :
    |y t - u| ≤ |y tk - u| := by
  have herr := settlingError_eq tau u tk tk1 htau htk y hcont hdiff hode t ht
  have hexp_arg : -(t - tk) / tau ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · have hle : 0 ≤ t - tk := sub_nonneg.mpr ht.1
      linarith
    · exact le_of_lt htau
  have hexp_le_one : Real.exp (-(t - tk) / tau) ≤ 1 :=
    Real.exp_le_one_iff.mpr hexp_arg
  calc |y t - u| = |y tk - u| * Real.exp (-(t - tk) / tau) := herr
    _ ≤ |y tk - u| * 1 := mul_le_mul_of_nonneg_left hexp_le_one (abs_nonneg _)
    _ = |y tk - u| := mul_one _

/-- Two holding intervals with a change of level at the junction:
an output continuous on the whole span, obeying the first held
equation on the first open interval and the second on the
second, is given on the second interval by the settling output
whose initial value is the first interval's endpoint value, for
`tau > 0` and `tk < tk1 < tk2`. Continuity at the junction is
the no-reset hypothesis. -/
lemma heldOutput_twoIntervals (tau u1 u2 tk tk1 tk2 : ℝ) (htau : 0 < tau)
    (htk : tk < tk1) (htk2 : tk1 < tk2) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk2))
    (hdiff1 : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hdiff2 : ∀ s : ℝ, s ∈ Set.Ioo tk1 tk2 → DifferentiableAt ℝ y s)
    (hode1 : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → tau * deriv y s = u1 - y s)
    (hode2 : ∀ s : ℝ, s ∈ Set.Ioo tk1 tk2 → tau * deriv y s = u2 - y s)
    (t : ℝ) (ht : t ∈ Set.Icc tk1 tk2) :
    y t = settlingOutput u2
      (u1 + (y tk - u1) * Real.exp (-(tk1 - tk) / tau)) tk1 tau t := by
  have hcont1 : ContinuousOn y (Set.Icc tk tk1) :=
    hcont.mono (Set.Icc_subset_Icc le_rfl (le_of_lt htk2))
  have hcont2 : ContinuousOn y (Set.Icc tk1 tk2) :=
    hcont.mono (Set.Icc_subset_Icc (le_of_lt htk) le_rfl)
  have h_end := heldOutput_endpoint_recurrence tau u1 tk tk1 htau htk y hcont1 hdiff1 hode1
  have h_main := heldOutput_eq_settlingOutput tau u2 tk1 tk2 htau htk2 y hcont2 hdiff2 hode2 t ht
  rw [h_end] at h_main
  exact h_main

/-- Code-held settling: when the held level is the actual level
of an integer code from the converter level model, the settling
error on the interval is measured against that actual level,
under the same first-order hypotheses with that level held. -/
lemma codeHeld_settlingError_eq (tau Δ : ℝ) (htau : 0 < tau) (e : ℤ → ℝ)
    (k : ℤ) (tk tk1 : ℝ) (htk : tk < tk1) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk1))
    (hdiff : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hode : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 →
      tau * deriv y s = dacLevel Δ e k - y s)
    (t : ℝ) (ht : t ∈ Set.Icc tk tk1) :
    |y t - dacLevel Δ e k| =
      |y tk - dacLevel Δ e k| * Real.exp (-(t - tk) / tau) := by
  exact settlingError_eq tau (dacLevel Δ e k) tk tk1 htau htk y hcont hdiff hode t ht

/-- Headline: on one holding interval with `tau > 0` and
`tk < tk1`, a continuous output obeying `tau * y' = u - y` at
every interior time is the explicit settling output, its right
endpoint obeys the endpoint recurrence, and its settling error
is the initial mismatch times the exponential factor. -/
theorem settling_correct (tau u tk tk1 : ℝ) (htau : 0 < tau)
    (htk : tk < tk1) (y : ℝ → ℝ)
    (hcont : ContinuousOn y (Set.Icc tk tk1))
    (hdiff : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → DifferentiableAt ℝ y s)
    (hode : ∀ s : ℝ, s ∈ Set.Ioo tk tk1 → tau * deriv y s = u - y s) :
    (∀ t : ℝ, t ∈ Set.Icc tk tk1 →
      y t = settlingOutput u (y tk) tk tau t) ∧
    y tk1 = u + (y tk - u) * Real.exp (-(tk1 - tk) / tau) ∧
    (∀ t : ℝ, t ∈ Set.Icc tk tk1 →
      |y t - u| = |y tk - u| * Real.exp (-(t - tk) / tau)) := by
  exact ⟨fun t ht => heldOutput_eq_settlingOutput tau u tk tk1 htau htk y hcont hdiff hode t ht,
    heldOutput_endpoint_recurrence tau u tk tk1 htau htk y hcont hdiff hode,
    fun t ht => settlingError_eq tau u tk tk1 htau htk y hcont hdiff hode t ht⟩

end PhyslibExt.Instrumentation.HeldDACSettling
