/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14(vi)

Closed form for ∫₀ˣ 1/(1+u⁶) du via arctan and log terms.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry14ViIntegral6

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)

/-- **Ramanujan's closed form for $\int_0^x du/(1 + u^6)$ (Chapter 8, Entry 14(vi)).** For every
real number $x$, the function $u \mapsto 1/(1 + u^6)$ is integrable on the interval between $0$
and $x$, $1 + \sqrt3\,x + x^2 > 0$, $1 - \sqrt3\,x + x^2 > 0$, and
$$\int_0^x \frac{du}{1 + u^6} = \frac12 \arctan x + \frac16 \arctan x^3 +
\frac{1}{4\sqrt3} \log \frac{1 + \sqrt3\,x + x^2}{1 - \sqrt3\,x + x^2}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8,
Entry 14(vi), pp. 189–190.
Proves `Wanted` entry `ramanujan_part1_ch8_entry14_vi_integral6`.
-/
theorem ramanujan_part1_ch8_entry14_vi_integral6 (x : ℝ) :
    IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (6 : ℕ))) volume 0 x ∧
      0 < 1 + x * Real.sqrt 3 + x ^ 2 ∧
      0 < 1 - x * Real.sqrt 3 + x ^ 2 ∧
      chapter8Entry14A 6 x =
        (1 / 2 : ℝ) * Real.arctan x +
          (1 / 6 : ℝ) * Real.arctan (x ^ 3) +
          1 / (4 * Real.sqrt 3) *
            Real.log
              ((1 + x * Real.sqrt 3 + x ^ 2) /
                (1 - x * Real.sqrt 3 + x ^ 2)) := by
  have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hsne : Real.sqrt 3 ≠ 0 := ne_of_gt hspos
  have hN : ∀ t : ℝ, 0 < 1 + t * Real.sqrt 3 + t ^ 2 := by
    intro t
    nlinarith [sq_nonneg (t + Real.sqrt 3 / 2)]
  have hD : ∀ t : ℝ, 0 < 1 - t * Real.sqrt 3 + t ^ 2 := by
    intro t
    nlinarith [sq_nonneg (t - Real.sqrt 3 / 2)]
  have hF0 : (1 / 2 : ℝ) * Real.arctan (0 : ℝ) +
      (1 / 6 : ℝ) * Real.arctan ((0 : ℝ) ^ 3) +
      1 / (4 * Real.sqrt 3) *
        Real.log
          ((1 + (0 : ℝ) * Real.sqrt 3 + (0 : ℝ) ^ 2) /
            (1 - (0 : ℝ) * Real.sqrt 3 + (0 : ℝ) ^ 2)) = 0 := by
    simp
  have hDeriv : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => (1 / 2 : ℝ) * Real.arctan t +
        (1 / 6 : ℝ) * Real.arctan (t ^ 3) +
        1 / (4 * Real.sqrt 3) *
          Real.log
            ((1 + t * Real.sqrt 3 + t ^ 2) /
              (1 - t * Real.sqrt 3 + t ^ 2)))
      (1 / (1 + t ^ 6)) t := by
    intro t
    have hDne : (1 - t * Real.sqrt 3 + t ^ 2) ≠ 0 := ne_of_gt (hD t)
    have hNne : (1 + t * Real.sqrt 3 + t ^ 2) ≠ 0 := ne_of_gt (hN t)
    have h1p2 : (1 + t ^ 2) ≠ 0 := by positivity
    have h1p6 : (1 + t ^ 6) ≠ 0 := by positivity
    have hND : (1 + t * Real.sqrt 3 + t ^ 2) / (1 - t * Real.sqrt 3 + t ^ 2) ≠ 0 :=
      div_ne_zero hNne hDne
    have e1 : HasDerivAt (fun t : ℝ => (1 / 2 : ℝ) * Real.arctan t)
        ((1 / 2 : ℝ) * (1 / (1 + t ^ 2))) t :=
      (Real.hasDerivAt_arctan t).const_mul (1 / 2)
    have hpow3 : HasDerivAt (fun t : ℝ => t ^ 3) ((3 : ℝ) * t ^ 2) t := by
      simpa using hasDerivAt_pow 3 t
    have earctan : HasDerivAt (fun t : ℝ => Real.arctan (t ^ 3))
        (1 / (1 + (t ^ 3) ^ 2) * ((3 : ℝ) * t ^ 2)) t :=
      hpow3.arctan
    have e2 : HasDerivAt (fun t : ℝ => (1 / 6 : ℝ) * Real.arctan (t ^ 3))
        ((1 / 6 : ℝ) * (1 / (1 + (t ^ 3) ^ 2) * ((3 : ℝ) * t ^ 2))) t :=
      earctan.const_mul (1 / 6)
    have hNderiv : HasDerivAt (fun t : ℝ => 1 + t * Real.sqrt 3 + t ^ 2)
        (Real.sqrt 3 + 2 * t) t := by
      have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
      have h2 : HasDerivAt (fun t : ℝ => t * Real.sqrt 3) (1 * Real.sqrt 3) t :=
        (hasDerivAt_id t).mul_const _
      have h3 : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℝ) * t) t := by
        simpa using hasDerivAt_pow 2 t
      have h := (h1.add h2).add h3
      convert h using 1
      ring
    have hDderiv : HasDerivAt (fun t : ℝ => 1 - t * Real.sqrt 3 + t ^ 2)
        (-Real.sqrt 3 + 2 * t) t := by
      have h1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 t := hasDerivAt_const t 1
      have h2 : HasDerivAt (fun t : ℝ => t * Real.sqrt 3) (1 * Real.sqrt 3) t :=
        (hasDerivAt_id t).mul_const _
      have h3 : HasDerivAt (fun t : ℝ => t ^ 2) ((2 : ℝ) * t) t := by
        simpa using hasDerivAt_pow 2 t
      have h := (h1.sub h2).add h3
      convert h using 1
      ring
    have hR : HasDerivAt
        (fun t : ℝ => (1 + t * Real.sqrt 3 + t ^ 2) / (1 - t * Real.sqrt 3 + t ^ 2))
        (((Real.sqrt 3 + 2 * t) * (1 - t * Real.sqrt 3 + t ^ 2) -
          (1 + t * Real.sqrt 3 + t ^ 2) * (-Real.sqrt 3 + 2 * t)) /
          (1 - t * Real.sqrt 3 + t ^ 2) ^ 2) t :=
      hNderiv.div hDderiv hDne
    have hlog : HasDerivAt
        (fun t : ℝ => Real.log ((1 + t * Real.sqrt 3 + t ^ 2) /
          (1 - t * Real.sqrt 3 + t ^ 2)))
        ((((Real.sqrt 3 + 2 * t) * (1 - t * Real.sqrt 3 + t ^ 2) -
          (1 + t * Real.sqrt 3 + t ^ 2) * (-Real.sqrt 3 + 2 * t)) /
          (1 - t * Real.sqrt 3 + t ^ 2) ^ 2) /
          ((1 + t * Real.sqrt 3 + t ^ 2) / (1 - t * Real.sqrt 3 + t ^ 2))) t :=
      hR.log hND
    have e3 : HasDerivAt
        (fun t : ℝ => 1 / (4 * Real.sqrt 3) * Real.log ((1 + t * Real.sqrt 3 + t ^ 2) /
          (1 - t * Real.sqrt 3 + t ^ 2)))
        (1 / (4 * Real.sqrt 3) * ((((Real.sqrt 3 + 2 * t) *
          (1 - t * Real.sqrt 3 + t ^ 2) -
          (1 + t * Real.sqrt 3 + t ^ 2) * (-Real.sqrt 3 + 2 * t)) /
          (1 - t * Real.sqrt 3 + t ^ 2) ^ 2) /
          ((1 + t * Real.sqrt 3 + t ^ 2) / (1 - t * Real.sqrt 3 + t ^ 2)))) t :=
      hlog.const_mul (1 / (4 * Real.sqrt 3))
    have key1 : ((Real.sqrt 3 + 2 * t) * (1 - t * Real.sqrt 3 + t ^ 2) -
        (1 + t * Real.sqrt 3 + t ^ 2) * (-Real.sqrt 3 + 2 * t))
        = 2 * Real.sqrt 3 * (1 - t ^ 2) := by ring
    have key2' : (1 + t * Real.sqrt 3 + t ^ 2) * (1 - t * Real.sqrt 3 + t ^ 2)
        = 1 - t ^ 2 + t ^ 4 := by
      linear_combination (-(t ^ 2)) * hsq
    have hNDprod : (1 + t * Real.sqrt 3 + t ^ 2) * (1 - t * Real.sqrt 3 + t ^ 2) ≠ 0 :=
      mul_ne_zero hNne hDne
    have h14 : (1 - t ^ 2 + t ^ 4) ≠ 0 := by rw [← key2']; exact hNDprod
    have hlogsimp : ((((Real.sqrt 3 + 2 * t) * (1 - t * Real.sqrt 3 + t ^ 2) -
        (1 + t * Real.sqrt 3 + t ^ 2) * (-Real.sqrt 3 + 2 * t)) /
        (1 - t * Real.sqrt 3 + t ^ 2) ^ 2) /
        ((1 + t * Real.sqrt 3 + t ^ 2) / (1 - t * Real.sqrt 3 + t ^ 2)))
        = (2 * Real.sqrt 3 * (1 - t ^ 2)) /
          ((1 + t * Real.sqrt 3 + t ^ 2) * (1 - t * Real.sqrt 3 + t ^ 2)) := by
      rw [key1]; field_simp
    have hlogsimp2 : (1 / (4 * Real.sqrt 3)) * ((((Real.sqrt 3 + 2 * t) *
        (1 - t * Real.sqrt 3 + t ^ 2) -
        (1 + t * Real.sqrt 3 + t ^ 2) * (-Real.sqrt 3 + 2 * t)) /
        (1 - t * Real.sqrt 3 + t ^ 2) ^ 2) /
        ((1 + t * Real.sqrt 3 + t ^ 2) / (1 - t * Real.sqrt 3 + t ^ 2)))
        = (1 - t ^ 2) / (2 * (1 - t ^ 2 + t ^ 4)) := by
      rw [hlogsimp, key2']; field_simp; ring
    have key0 : (t ^ 3) ^ 2 = t ^ 6 := by ring
    have hfinal : (1 / 2 : ℝ) * (1 / (1 + t ^ 2)) +
        (1 / 6 : ℝ) * (1 / (1 + (t ^ 3) ^ 2) * ((3 : ℝ) * t ^ 2)) +
        (1 - t ^ 2) / (2 * (1 - t ^ 2 + t ^ 4)) = 1 / (1 + t ^ 6) := by
      rw [key0]; field_simp; ring
    have h := (e1.add e2).add e3
    rw [hlogsimp2, hfinal] at h
    exact h
  have hden : ∀ u : ℝ, (1 : ℝ) + u ^ (6 : ℕ) ≠ 0 := fun u => by positivity
  have hcont : Continuous (fun u : ℝ => 1 / (1 + u ^ (6 : ℕ))) :=
    continuous_const.div (continuous_const.add (continuous_id.pow 6)) (fun u => hden u)
  have hint : IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (6 : ℕ))) volume 0 x :=
    hcont.intervalIntegrable 0 x
  have hInt : (∫ u in (0 : ℝ)..x, 1 / (1 + u ^ (6 : ℕ))) =
      ((1 / 2 : ℝ) * Real.arctan x +
        (1 / 6 : ℝ) * Real.arctan (x ^ 3) +
        1 / (4 * Real.sqrt 3) *
          Real.log
            ((1 + x * Real.sqrt 3 + x ^ 2) /
              (1 - x * Real.sqrt 3 + x ^ 2))) -
      ((1 / 2 : ℝ) * Real.arctan (0 : ℝ) +
        (1 / 6 : ℝ) * Real.arctan ((0 : ℝ) ^ 3) +
        1 / (4 * Real.sqrt 3) *
          Real.log
            ((1 + (0 : ℝ) * Real.sqrt 3 + (0 : ℝ) ^ 2) /
              (1 - (0 : ℝ) * Real.sqrt 3 + (0 : ℝ) ^ 2))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hDeriv y) hint
  refine ⟨hint, hN x, hD x, ?_⟩
  show chapter8Entry14A 6 x = _
  unfold chapter8Entry14A
  rw [hInt, hF0, sub_zero]

end

end Entry14ViIntegral6

end MathlibExt.Analysis.Ramanujan.Part1Ch8
