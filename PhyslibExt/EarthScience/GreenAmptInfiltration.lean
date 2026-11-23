/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.LinearCombination

/-!
# Unsaturated flow and infiltration: Green-Ampt

For ponded Green-Ampt infiltration `F' = K (1 + A / F)` on an interval
`[t₀, t]` with `K > 0`, `A ≥ 0` and `F > 0` there, integrating gives
`t - t₀ = (F - F₀ - A log ((F + A) / (F₀ + A))) / K`. With no suction
head (`A = 0`) this reduces to constant-rate infiltration, which needs no
positivity of `F` and so also covers the dry start `F₀ = 0`.

## i. Overview

Green and Ampt model ponded infiltration into a uniform soil by a sharp
wetting front. Here `F` is the cumulative infiltration depth, `K > 0` the
saturated hydraulic conductivity, and `A = ψ Δθ ≥ 0` the wetting-front
suction head `ψ` times the moisture deficit `Δθ`; the infiltration rate is
`F' = K (1 + A / F)`. The standard statement starts ponding at `t = 0`
with `F(0) = 0` and integrates to `K t = F - A log (1 + F / A)`. Because
the rate is singular at `F = 0` when `A > 0`, the general theorem here
starts instead from a positive cumulative depth `F(t₀) = F₀ > 0` at any time
`t₀`; the standard form is the limiting case `t₀ = 0`, `F₀ → 0⁺`.

The hypotheses are stated on the interval `[t₀, t]`, where they are
satisfiable (e.g. `K = 1`, `A = 0`, `F(s) = s + 2` on `[0, 1]`). The
proof goes through the antiderivative `G(F) = F - A log (F + A)`,
whose derivative along `F` is the constant `K`: indeed
`G'(F) = F / (F + A) = 1 / (1 + A / F)`. The fundamental theorem of
calculus then gives `G(F(t)) - G(F(t₀)) = K (t - t₀)`. This is a
sharp-front empirical model with unlimited ponded supply; for `A > 0` the
dry initial state `F₀ = 0` is a separate limit and is not proved here, while
for `A = 0` the rate is the constant `K` and `green_ampt_no_suction` covers
it.

## ii. Key results

- `EarthScience.green_ampt_integrated`: the integrated Green-Ampt law.
- `EarthScience.green_ampt_no_suction`: the `A = 0` case, without positivity
  hypotheses on `F`, so including the dry start `F₀ = 0`.

## iii. Table of contents

- A. Integrated Green-Ampt law

## iv. References

- W. H. Green and G. A. Ampt, "Studies on soil physics, Part I: The flow
  of air and water through soils", *J. Agric. Sci.* 4 (1911), 1-24: the
  sharp-wetting-front infiltration model.
- V. T. Chow, D. R. Maidment and L. W. Mays, *Applied Hydrology*,
  McGraw-Hill, 1988, Chapter 4 (Subsurface water), the Green-Ampt method:
  the infiltration rate `f = K (ψ Δθ / F + 1)` and, for ponding from
  `F(0) = 0`, the cumulative infiltration `F - ψ Δθ log (1 + F / (ψ Δθ)) = K t`.
- `intervalIntegral.integral_eq_sub_of_hasDerivAt` in
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean`
  (Mathlib).

## A. Integrated Green-Ampt law
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace EarthScience

/-- Green-Ampt integrated infiltration law on an interval `[t₀, t]`. If
`F t₀ = F₀`, `F s > 0` for `s ∈ [t₀, t]`, and `F` obeys the ponded
Green-Ampt ODE `F' = K (1 + A / F)` on `[t₀, t]` with `K > 0`, `A ≥ 0`,
then integrating gives
`t - t₀ = (F t - F₀ - A log ((F t + A) / (F₀ + A))) / K`. The proof goes
through the antiderivative `G(F) = F - A log (F + A)`, whose derivative
along `F` is the constant `K`. The hypotheses are satisfiable: e.g.
`K = 1, A = 0, F s = s + 2` on `[0, 1]` meets them with `F₀ = 2`. -/
theorem green_ampt_integrated (F : ℝ → ℝ) (K A F₀ t₀ t : ℝ) (hK : 0 < K)
    (hA : 0 ≤ A) (hF₀ : 0 < F₀) (ht : t₀ ≤ t)
    (hFpos : ∀ s ∈ Set.Icc t₀ t, F s > 0)
    (hF₀eq : F t₀ = F₀)
    (hode : ∀ s ∈ Set.Icc t₀ t, HasDerivAt F (K * (1 + A / F s)) s) :
    t - t₀ = (F t - F₀ - A * Real.log ((F t + A) / (F₀ + A))) / K := by
  have hKne : K ≠ 0 := ne_of_gt hK
  have hFt_pos : 0 < F t := hFpos t ⟨ht, le_rfl⟩
  have hFtA_ne : F t + A ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hFt_pos hA)
  have hF0A_ne : F₀ + A ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hF₀ hA)
  -- The antiderivative `G (F s) = F s - A * log (F s + A)` has constant derivative `K`.
  have hH : ∀ s ∈ Set.Icc t₀ t,
      HasDerivAt (fun s => F s - A * Real.log (F s + A)) K s := by
    intro s hs
    have hFs_ne : F s ≠ 0 := ne_of_gt (hFpos s hs)
    have hFsA_ne : F s + A ≠ 0 :=
      ne_of_gt (add_pos_of_pos_of_nonneg (hFpos s hs) hA)
    have h_inner : HasDerivAt (fun x => x + A) 1 (F s) :=
      (hasDerivAt_id' (F s)).add_const A
    have hlog : HasDerivAt (fun x => Real.log (x + A)) (1 / (F s + A)) (F s) :=
      h_inner.log hFsA_ne
    have hAmul : HasDerivAt (fun x => A * Real.log (x + A)) (A * (1 / (F s + A))) (F s) :=
      hlog.const_mul A
    have hsub : HasDerivAt (fun x => x - A * Real.log (x + A))
        (1 - A * (1 / (F s + A))) (F s) :=
      (hasDerivAt_id' (F s)).sub hAmul
    have hval : (1 - A * (1 / (F s + A))) * (K * (1 + A / F s)) = K := by
      field_simp
      ring
    have hc := hsub.comp s (hode s hs)
    rw [hval] at hc
    have h : HasDerivAt ((fun x => x - A * Real.log (x + A)) ∘ F) K s := by
      simpa using hc
    exact h
  have huIcc : Set.uIcc t₀ t = Set.Icc t₀ t := Set.uIcc_of_le ht
  have hint : IntervalIntegrable (fun _ => K) volume t₀ t := intervalIntegrable_const
  have hderiv : ∀ x ∈ Set.uIcc t₀ t,
      HasDerivAt (fun s => F s - A * Real.log (F s + A)) K x := by
    intro x hx
    rw [huIcc] at hx
    exact hH x hx
  have hFTC_H : (∫ s in t₀..t, K) =
      (F t - A * Real.log (F t + A)) - (F t₀ - A * Real.log (F t₀ + A)) := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := fun s => F s - A * Real.log (F s + A)) (f' := fun _ => K) hderiv hint
    simpa using h
  have hderiv_lin : ∀ x ∈ Set.uIcc t₀ t, HasDerivAt (fun s => K * s) K x := by
    intro x _
    simpa using (hasDerivAt_id' x).const_mul K
  have hFTC_lin : (∫ s in t₀..t, K) = K * t - K * t₀ := by
    have h := integral_eq_sub_of_hasDerivAt
      (f := fun s => K * s) (f' := fun _ => K) hderiv_lin hint
    simpa using h
  have hHeq : (F t - A * Real.log (F t + A)) - (F t₀ - A * Real.log (F t₀ + A))
      = K * t - K * t₀ := by
    rw [← hFTC_H, ← hFTC_lin]
  rw [hF₀eq] at hHeq
  have hlog : Real.log ((F t + A) / (F₀ + A))
      = Real.log (F t + A) - Real.log (F₀ + A) :=
    Real.log_div hFtA_ne hF0A_ne
  rw [hlog, eq_div_iff hKne]
  linear_combination -hHeq

/-- Green-Ampt with no suction head (`A = 0`) reduces to constant-rate
infiltration: `t - t₀ = (F t - F₀) / K`. The rate `K * (1 + 0 / F s)` is the
constant `K` whatever the value of `F s`, so no positivity of `F` or `F₀` is
assumed; in particular the dry start `F t₀ = F₀ = 0` is covered. -/
theorem green_ampt_no_suction (F : ℝ → ℝ) (K F₀ t₀ t : ℝ) (hK : 0 < K)
    (ht : t₀ ≤ t)
    (hF₀eq : F t₀ = F₀)
    (hode : ∀ s ∈ Set.Icc t₀ t, HasDerivAt F (K * (1 + 0 / F s)) s) :
    t - t₀ = (F t - F₀) / K := by
  have hderiv : ∀ x ∈ Set.uIcc t₀ t, HasDerivAt F K x := by
    intro x hx
    rw [Set.uIcc_of_le ht] at hx
    simpa using hode x hx
  have hint : IntervalIntegrable (fun _ => K) volume t₀ t := intervalIntegrable_const
  have h := integral_eq_sub_of_hasDerivAt (f := F) (f' := fun _ => K) hderiv hint
  rw [intervalIntegral.integral_const, smul_eq_mul, hF₀eq] at h
  rw [eq_div_iff (ne_of_gt hK)]
  exact h

end EarthScience
