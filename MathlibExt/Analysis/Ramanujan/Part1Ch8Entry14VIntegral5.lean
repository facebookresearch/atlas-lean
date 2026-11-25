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
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14(v)

Closed form for ∫₀ˣ 1/(1+u⁵) du via log and arctan terms.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry14VIntegral5

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)

/-- **Ramanujan's closed form for $\int_0^x du/(1 + u^5)$ (Chapter 8, Entry 14(v)).** Let $x$ be
a real number with $-1 < x < 4/(\sqrt5 + 1)$, and put $c_\pm = \sqrt{10 \pm 2\sqrt5}$ and
$$Q(x) = \frac{1 + \tfrac12 x(\sqrt5 - 1) + x^2}{1 - \tfrac12 x(\sqrt5 + 1) + x^2}.$$
Then $u \mapsto 1/(1 + u^5)$ is integrable on the interval between $0$ and $x$,
$(1 + x)^5/(1 + x^5) > 0$, $Q(x) > 0$, $4 + x(\sqrt5 - 1) \ne 0$, $4 - x(\sqrt5 + 1) \ne 0$, and
$$\int_0^x \frac{du}{1 + u^5} = \frac{1}{20} \log \frac{(1 + x)^5}{1 + x^5} +
\frac{1}{4\sqrt5} \log Q(x) + \frac{c_+}{10} \arctan \frac{c_+ x}{4 + x(\sqrt5 - 1)} +
\frac{c_-}{10} \arctan \frac{c_- x}{4 - x(\sqrt5 + 1)}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8,
Entry 14(v), pp. 189–191.
Proves `Wanted` entry `ramanujan_part1_ch8_entry14_v_integral5`.
-/
theorem ramanujan_part1_ch8_entry14_v_integral5 (x : ℝ) (hxLower : -1 < x)
    (hxUpper : x < 4 / (Real.sqrt 5 + 1)) :
    IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (5 : ℕ))) volume 0 x ∧
      0 < (1 + x) ^ 5 / (1 + x ^ 5) ∧
      0 <
        (1 + (1 / 2 : ℝ) * x * (Real.sqrt 5 - 1) + x ^ 2) /
          (1 - (1 / 2 : ℝ) * x * (Real.sqrt 5 + 1) + x ^ 2) ∧
      4 + x * (Real.sqrt 5 - 1) ≠ 0 ∧
      4 - x * (Real.sqrt 5 + 1) ≠ 0 ∧
      chapter8Entry14A 5 x =
        (1 / 20 : ℝ) * Real.log ((1 + x) ^ 5 / (1 + x ^ 5)) +
          1 / (4 * Real.sqrt 5) *
            Real.log
              ((1 + (1 / 2 : ℝ) * x * (Real.sqrt 5 - 1) + x ^ 2) /
                (1 - (1 / 2 : ℝ) * x * (Real.sqrt 5 + 1) + x ^ 2)) +
          (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
            Real.arctan
              (x * Real.sqrt (10 + 2 * Real.sqrt 5) /
                (4 + x * (Real.sqrt 5 - 1))) +
          (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
            Real.arctan
              (x * Real.sqrt (10 - 2 * Real.sqrt 5) /
                (4 - x * (Real.sqrt 5 + 1))) := by
  -- Basic facts about √5.
  have hs_sq : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs_nonneg : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hs_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hs_gt_one : (1 : ℝ) < Real.sqrt 5 := by nlinarith [hs_sq, hs_nonneg]
  have hs_lt_three : Real.sqrt 5 < (3 : ℝ) := by nlinarith [hs_sq, hs_nonneg]
  have hs1ne : Real.sqrt 5 + 1 ≠ 0 := ne_of_gt (by linarith)
  have h4 : (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) = 4 := by
    linear_combination hs_sq
  -- Reformulated upper bound: x < √5 - 1.
  have hx4 : x * (Real.sqrt 5 + 1) < 4 := by
    have h := hxUpper
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < Real.sqrt 5 + 1)] at h
    linarith [h]
  have hxUpper' : x < Real.sqrt 5 - 1 := by
    have h2 : x * (Real.sqrt 5 + 1) < (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) := by
      rw [h4]; exact hx4
    exact lt_of_mul_lt_mul_right h2 (by linarith)
  -- The two quadratics are always positive (complete the square).
  have hQ1 : ∀ u : ℝ, (0 : ℝ) < 1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2 := by
    intro u
    have hsq : (1 : ℝ) + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2
        = (u + (Real.sqrt 5 - 1) / 4) ^ 2 + (5 + Real.sqrt 5) / 8 := by
      linear_combination (-1 / 16) * hs_sq
    rw [hsq]
    have hnn := sq_nonneg (u + (Real.sqrt 5 - 1) / 4)
    linarith [hs_pos]
  have hQ2 : ∀ u : ℝ, (0 : ℝ) < 1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2 := by
    intro u
    have hsq : (1 : ℝ) - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2
        = (u - (Real.sqrt 5 + 1) / 4) ^ 2 + (5 - Real.sqrt 5) / 8 := by
      linear_combination (-1 / 16) * hs_sq
    rw [hsq]
    have hnn := sq_nonneg (u - (Real.sqrt 5 + 1) / 4)
    linarith [hs_lt_three]
  -- Factorization of 1 + u^5.
  have hfact : ∀ u : ℝ, (1 : ℝ) + u ^ 5 = (1 + u) *
      (1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2) *
      (1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2) := by
    intro u
    have h : (1 + u) *
        (1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2) *
        (1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2)
        - (1 + u ^ 5)
        = -((1 + u) * u ^ 2 / 4) * ((Real.sqrt 5) ^ 2 - 5) := by
      ring
    linear_combination -h + ((1 + u) * u ^ 2 / 4) * hs_sq
  -- Every point of the integration interval lies in (-1, √5 - 1).
  have hmem : ∀ u : ℝ, u ∈ Set.uIcc 0 x → (-1 < u ∧ u < Real.sqrt 5 - 1) := by
    intro u hu
    rw [Set.mem_uIcc] at hu
    rcases hu with ⟨h0, hx⟩ | ⟨hx, h0⟩
    · exact ⟨by linarith, by linarith [hxUpper']⟩
    · exact ⟨by linarith [hxLower], by linarith [hs_gt_one]⟩
  have h1u : ∀ u ∈ Set.uIcc 0 x, (0 : ℝ) < 1 + u := by
    intro u hu
    linarith [(hmem u hu).1]
  have hDu : ∀ u ∈ Set.uIcc 0 x, (1 : ℝ) + u ^ 5 ≠ 0 := by
    intro u hu
    rw [hfact u]
    exact ne_of_gt (mul_pos (mul_pos (h1u u hu) (hQ1 u)) (hQ2 u))
  have hInt : IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (5 : ℕ))) volume 0 x := by
    have hg : Continuous (fun u : ℝ => (1 : ℝ) + u ^ 5) := by continuity
    exact ContinuousOn.intervalIntegrable
      (ContinuousOn.div (f := fun _ : ℝ => (1 : ℝ))
        (g := fun u : ℝ => (1 : ℝ) + u ^ 5)
        continuousOn_const hg.continuousOn (fun u hu => hDu u hu))
  -- Side conditions at x.
  have h1x : (0 : ℝ) < 1 + x := by linarith
  have hDx : (0 : ℝ) < 1 + x ^ 5 := by
    rw [hfact x]
    exact mul_pos (mul_pos h1x (hQ1 x)) (hQ2 x)
  have hL1 : (0 : ℝ) < (1 + x) ^ 5 / (1 + x ^ 5) :=
    div_pos (pow_pos h1x 5) hDx
  have hL2 : (0 : ℝ) < (1 + (1 / 2 : ℝ) * x * (Real.sqrt 5 - 1) + x ^ 2) /
      (1 - (1 / 2 : ℝ) * x * (Real.sqrt 5 + 1) + x ^ 2) :=
    div_pos (hQ1 x) (hQ2 x)
  have hne1 : 4 + x * (Real.sqrt 5 - 1) ≠ 0 := by
    apply ne_of_gt
    have hpos : (0 : ℝ) < Real.sqrt 5 - 1 := by linarith
    have hmul := mul_lt_mul_of_pos_right hxLower hpos
    simp only [neg_mul, one_mul] at hmul
    linarith [hs_lt_three]
  have hne2 : 4 - x * (Real.sqrt 5 + 1) ≠ 0 := by
    apply ne_of_gt
    linarith [hx4]
  -- Value of the antiderivative at 0.
  have hF0 : (1 / 20 : ℝ) * Real.log ((1 + 0) ^ 5 / (1 + 0 ^ 5)) +
      1 / (4 * Real.sqrt 5) *
        Real.log ((1 + (1 / 2 : ℝ) * 0 * (Real.sqrt 5 - 1) + 0 ^ 2) /
          (1 - (1 / 2 : ℝ) * 0 * (Real.sqrt 5 + 1) + 0 ^ 2)) +
      (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
        Real.arctan (0 * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + 0 * (Real.sqrt 5 - 1))) +
      (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
        Real.arctan (0 * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - 0 * (Real.sqrt 5 + 1))) = 0 := by
    simp
  -- Derivative of the closed form at each point of the interval.
  have hderiv : ∀ t ∈ Set.uIcc 0 x, HasDerivAt
      (fun t => (1 / 20 : ℝ) * Real.log ((1 + t) ^ 5 / (1 + t ^ 5)) +
        1 / (4 * Real.sqrt 5) *
          Real.log ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
        (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
            (4 + t * (Real.sqrt 5 - 1))) +
        (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
            (4 - t * (Real.sqrt 5 + 1))))
      ((fun u : ℝ => 1 / (1 + u ^ 5)) t) t := by
    intro t ht
    have hbt := hmem t ht
    have ht1 : (-1 : ℝ) < t := hbt.1
    have ht2 : t < Real.sqrt 5 - 1 := hbt.2
    have h1t : (0 : ℝ) < 1 + t := by linarith
    have h1tne : (1 : ℝ) + t ≠ 0 := ne_of_gt h1t
    have hDt : (0 : ℝ) < 1 + t ^ 5 := by
      rw [hfact t]
      exact mul_pos (mul_pos h1t (hQ1 t)) (hQ2 t)
    have hD0ne : (1 : ℝ) + t ^ 5 ≠ 0 := ne_of_gt hDt
    have hQ1t : (0 : ℝ) < 1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2 :=
      hQ1 t
    have hQ2t : (0 : ℝ) < 1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2 :=
      hQ2 t
    have hQ1ne : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) ≠ 0 :=
      ne_of_gt hQ1t
    have hQ2ne : (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ≠ 0 :=
      ne_of_gt hQ2t
    have hL1ne : (1 + t) ^ 5 / (1 + t ^ 5) ≠ 0 :=
      div_ne_zero (pow_ne_zero 5 h1tne) hD0ne
    have hL2ne : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
        (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ≠ 0 :=
      div_ne_zero hQ1ne hQ2ne
    have hx4t : t * (Real.sqrt 5 + 1) < 4 := by
      calc t * (Real.sqrt 5 + 1)
          < (Real.sqrt 5 - 1) * (Real.sqrt 5 + 1) :=
            mul_lt_mul_of_pos_right ht2 (by linarith)
        _ = 4 := h4
    have hd1 : (4 : ℝ) + t * (Real.sqrt 5 - 1) ≠ 0 := by
      apply ne_of_gt
      have hpos : (0 : ℝ) < Real.sqrt 5 - 1 := by linarith
      have hmul := mul_lt_mul_of_pos_right ht1 hpos
      simp only [neg_mul, one_mul] at hmul
      linarith [hs_lt_three]
    have hd2 : (4 : ℝ) - t * (Real.sqrt 5 + 1) ≠ 0 := by
      apply ne_of_gt
      linarith [hx4t]
    -- Piece A: derivative of the first log term.
    have hnum : HasDerivAt (fun u : ℝ => (1 + u) ^ 5) (5 * (1 + t) ^ 4) t := by
      have h2 : HasDerivAt ((fun x : ℝ => 1 + x) ^ 5) (5 * (1 + t) ^ 4) t := by
        simpa using ((hasDerivAt_id t).const_add 1).pow 5
      exact h2
    have hden0 : HasDerivAt (fun u : ℝ => 1 + u ^ 5) (5 * t ^ 4) t := by
      have h2 : HasDerivAt (fun x : ℝ => 1 + x ^ 5) (5 * t ^ 4) t := by
        simpa using ((hasDerivAt_id t).pow 5).const_add 1
      exact h2
    have hdivA : HasDerivAt (fun u : ℝ => (1 + u) ^ 5 / (1 + u ^ 5))
        ((5 * (1 + t) ^ 4 * (1 + t ^ 5) - (1 + t) ^ 5 * (5 * t ^ 4)) /
          (1 + t ^ 5) ^ 2) t :=
      hnum.div hden0 hD0ne
    have hlogA : HasDerivAt
        (fun u : ℝ => Real.log ((1 + u) ^ 5 / (1 + u ^ 5)))
        (((5 * (1 + t) ^ 4 * (1 + t ^ 5) - (1 + t) ^ 5 * (5 * t ^ 4)) /
          (1 + t ^ 5) ^ 2) / ((1 + t) ^ 5 / (1 + t ^ 5))) t :=
      hdivA.log hL1ne
    have hA0 : HasDerivAt
        (fun u : ℝ => (1 / 20 : ℝ) * Real.log ((1 + u) ^ 5 / (1 + u ^ 5)))
        ((1 / 20 : ℝ) * (((5 * (1 + t) ^ 4 * (1 + t ^ 5) -
          (1 + t) ^ 5 * (5 * t ^ 4)) / (1 + t ^ 5) ^ 2) /
          ((1 + t) ^ 5 / (1 + t ^ 5)))) t :=
      hlogA.const_mul (1 / 20 : ℝ)
    -- Simplified form of the piece-A derivative.
    have hAsimp : ((5 * (1 + t) ^ 4 * (1 + t ^ 5) - (1 + t) ^ 5 * (5 * t ^ 4)) /
          (1 + t ^ 5) ^ 2) / ((1 + t) ^ 5 / (1 + t ^ 5)) =
        5 / (1 + t) - 5 * t ^ 4 /
          ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) := by
      rw [hfact t]
      generalize hQ1e : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) = Q1
      generalize hQ2e : (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) = Q2
      have hQ1t' : Q1 ≠ 0 := by rw [← hQ1e]; exact hQ1ne
      have hQ2t' : Q2 ≠ 0 := by rw [← hQ2e]; exact hQ2ne
      have hDne : (1 + t) * Q1 * Q2 ≠ 0 :=
        mul_ne_zero (mul_ne_zero h1tne hQ1t') hQ2t'
      have h1t5 : (1 + t) ^ 5 ≠ 0 := pow_ne_zero 5 h1tne
      field_simp
    have hA : HasDerivAt
        (fun u : ℝ => (1 / 20 : ℝ) * Real.log ((1 + u) ^ 5 / (1 + u ^ 5)))
        ((1 / 20 : ℝ) * (5 / (1 + t) - 5 * t ^ 4 /
          ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)))) t :=
      hAsimp ▸ hA0
    -- Piece B: derivative of the second log term.
    have hlin1 : HasDerivAt (fun u : ℝ => (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1))
        ((1 / 2 : ℝ) * (Real.sqrt 5 - 1)) t := by
      have hlin1' : HasDerivAt (fun u : ℝ => ((1 / 2 : ℝ) * (Real.sqrt 5 - 1)) * u)
          ((1 / 2 : ℝ) * (Real.sqrt 5 - 1)) t := by
        simpa using (hasDerivAt_id t).const_mul ((1 / 2 : ℝ) * (Real.sqrt 5 - 1))
      have hfun1 : (fun u : ℝ => (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1))
          = (fun u : ℝ => ((1 / 2 : ℝ) * (Real.sqrt 5 - 1)) * u) := by
        funext u
        ring
      rw [hfun1]
      exact hlin1'
    have hlin2 : HasDerivAt (fun u : ℝ => (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1))
        ((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) t := by
      have hlin2' : HasDerivAt (fun u : ℝ => ((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) * u)
          ((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) t := by
        simpa using (hasDerivAt_id t).const_mul ((1 / 2 : ℝ) * (Real.sqrt 5 + 1))
      have hfun2 : (fun u : ℝ => (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1))
          = (fun u : ℝ => ((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) * u) := by
        funext u
        ring
      rw [hfun2]
      exact hlin2'
    have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      have h2 : HasDerivAt ((id : ℝ → ℝ) ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_id t).pow 2
      exact h2
    have hQ1d : HasDerivAt
        (fun u : ℝ => 1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2)
        ((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) t := by
      have hcomb := ((hasDerivAt_const t (1 : ℝ)).add hlin1).add hsq
      have hmid : HasDerivAt
          (((fun _ : ℝ => (1 : ℝ)) + (fun u : ℝ => (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1))) +
            (fun u : ℝ => u ^ 2))
          ((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) t := by
        simpa using hcomb
      exact hmid
    have hQ2d : HasDerivAt
        (fun u : ℝ => 1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2)
        (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) t := by
      have hcomb := ((hasDerivAt_const t (1 : ℝ)).sub hlin2).add hsq
      have hmid : HasDerivAt
          (((fun _ : ℝ => (1 : ℝ)) - (fun u : ℝ => (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1))) +
            (fun u : ℝ => u ^ 2))
          (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) t := by
        simpa using hcomb
      exact hmid
    have hdivB : HasDerivAt
        (fun u : ℝ => (1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2) /
          (1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2))
        ((((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) -
          (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t)) /
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ^ 2) t :=
      hQ1d.div hQ2d hQ2ne
    have hlogB : HasDerivAt
        (fun u : ℝ => Real.log ((1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2) /
          (1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2)))
        (((((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) -
          (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t)) /
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ^ 2) /
          ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) t :=
      hdivB.log hL2ne
    have hB0 : HasDerivAt
        (fun u : ℝ => 1 / (4 * Real.sqrt 5) *
          Real.log ((1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2) /
            (1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2)))
        (1 / (4 * Real.sqrt 5) * (((((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) -
          (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t)) /
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ^ 2) /
          ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)))) t :=
      hlogB.const_mul (1 / (4 * Real.sqrt 5))
    have hBsimp : ((((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) *
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) -
        (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
          (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t)) /
        (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ^ 2) /
        ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) =
        ((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) /
          (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) -
        (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) /
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) := by
      generalize hQ1e : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) = Q1
      generalize hQ2e : (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) = Q2
      have hQ1t' : Q1 ≠ 0 := by rw [← hQ1e]; exact hQ1ne
      have hQ2t' : Q2 ≠ 0 := by rw [← hQ2e]; exact hQ2ne
      field_simp
    have hB : HasDerivAt
        (fun u : ℝ => 1 / (4 * Real.sqrt 5) *
          Real.log ((1 + (1 / 2 : ℝ) * u * (Real.sqrt 5 - 1) + u ^ 2) /
            (1 - (1 / 2 : ℝ) * u * (Real.sqrt 5 + 1) + u ^ 2)))
        (1 / (4 * Real.sqrt 5) *
          (((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) /
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) -
          (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) /
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) t :=
      hBsimp ▸ hB0
    -- Square facts for the arctan coefficients.
    have hk1sq : (Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 = 10 + 2 * Real.sqrt 5 :=
      Real.sq_sqrt (by linarith [hs_pos])
    have hk2sq : (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 = 10 - 2 * Real.sqrt 5 :=
      Real.sq_sqrt (by linarith [hs_lt_three])
    -- Piece C: derivative of the first arctan term.
    have hnum1 : HasDerivAt (fun u : ℝ => u * Real.sqrt (10 + 2 * Real.sqrt 5))
        (Real.sqrt (10 + 2 * Real.sqrt 5)) t := by
      simpa using (hasDerivAt_id t).mul_const (Real.sqrt (10 + 2 * Real.sqrt 5))
    have hden1 : HasDerivAt (fun u : ℝ => 4 + u * (Real.sqrt 5 - 1))
        (Real.sqrt 5 - 1) t := by
      have hlin3 : HasDerivAt (fun u : ℝ => u * (Real.sqrt 5 - 1))
          (Real.sqrt 5 - 1) t := by
        simpa using (hasDerivAt_id t).mul_const (Real.sqrt 5 - 1)
      exact hlin3.const_add 4
    have hu1div : HasDerivAt
        (fun u : ℝ => u * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + u * (Real.sqrt 5 - 1)))
        ((Real.sqrt (10 + 2 * Real.sqrt 5) * (4 + t * (Real.sqrt 5 - 1)) -
          t * Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) /
          (4 + t * (Real.sqrt 5 - 1)) ^ 2) t :=
      hnum1.div hden1 hd1
    have harctan1 : HasDerivAt
        (fun u : ℝ => Real.arctan (u * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + u * (Real.sqrt 5 - 1))))
        (1 / (1 + (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + t * (Real.sqrt 5 - 1))) ^ 2) *
          ((Real.sqrt (10 + 2 * Real.sqrt 5) * (4 + t * (Real.sqrt 5 - 1)) -
            t * Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) /
            (4 + t * (Real.sqrt 5 - 1)) ^ 2)) t :=
      hu1div.arctan
    have hC0 : HasDerivAt
        (fun u : ℝ => (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan (u * Real.sqrt (10 + 2 * Real.sqrt 5) /
            (4 + u * (Real.sqrt 5 - 1))))
        ((1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          (1 / (1 + (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
            (4 + t * (Real.sqrt 5 - 1))) ^ 2) *
            ((Real.sqrt (10 + 2 * Real.sqrt 5) * (4 + t * (Real.sqrt 5 - 1)) -
              t * Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) /
              (4 + t * (Real.sqrt 5 - 1)) ^ 2))) t :=
      harctan1.const_mul ((1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5))
    -- Simplified form of the piece-C derivative.
    have step1 : (Real.sqrt (10 + 2 * Real.sqrt 5) * (4 + t * (Real.sqrt 5 - 1)) -
          t * Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) /
          (4 + t * (Real.sqrt 5 - 1)) ^ 2 =
        4 * Real.sqrt (10 + 2 * Real.sqrt 5) / (4 + t * (Real.sqrt 5 - 1)) ^ 2 := by
      congr 1
      ring
    have e2 : (4 + t * (Real.sqrt 5 - 1)) ^ 2 +
        t ^ 2 * (10 + 2 * Real.sqrt 5) =
        16 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) := by
      linear_combination t ^ 2 * hs_sq
    have hden_eq : (1 + (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + t * (Real.sqrt 5 - 1))) ^ 2) * ((4 + t * (Real.sqrt 5 - 1)) ^ 2) =
        16 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) := by
      have eab : (1 + (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + t * (Real.sqrt 5 - 1))) ^ 2) * ((4 + t * (Real.sqrt 5 - 1)) ^ 2) =
          (4 + t * (Real.sqrt 5 - 1)) ^ 2 +
            t ^ 2 * (Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 := by
        have hM : ((4 : ℝ) + t * (Real.sqrt 5 - 1)) ^ 2 ≠ 0 :=
          pow_ne_zero 2 hd1
        field_simp
      rw [eab, hk1sq]
      exact e2
    have hu1e : (1 : ℝ) + (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
        (4 + t * (Real.sqrt 5 - 1))) ^ 2 =
        16 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
          ((4 + t * (Real.sqrt 5 - 1)) ^ 2) := by
      have hM : ((4 : ℝ) + t * (Real.sqrt 5 - 1)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 hd1
      rw [eq_div_iff hM]
      exact hden_eq
    have hd3 : ((1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5)) *
        (1 / (1 + (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
          (4 + t * (Real.sqrt 5 - 1))) ^ 2) *
          ((Real.sqrt (10 + 2 * Real.sqrt 5) * (4 + t * (Real.sqrt 5 - 1)) -
            t * Real.sqrt (10 + 2 * Real.sqrt 5) * (Real.sqrt 5 - 1)) /
            (4 + t * (Real.sqrt 5 - 1)) ^ 2)) =
        (5 + Real.sqrt 5) /
          (20 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2)) := by
      rw [step1, hu1e]
      generalize hQ1e : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) = Q1
      have hQ1t' : Q1 ≠ 0 := by rw [← hQ1e]; exact hQ1ne
      have hM : ((4 : ℝ) + t * (Real.sqrt 5 - 1)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 hd1
      have h16 : (16 : ℝ) * Q1 / ((4 + t * (Real.sqrt 5 - 1)) ^ 2) ≠ 0 :=
        div_ne_zero (mul_ne_zero (by norm_num) hQ1t') hM
      have hk1m : Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.sqrt (10 + 2 * Real.sqrt 5) = 10 + 2 * Real.sqrt 5 := by
        rw [← pow_two]
        exact hk1sq
      have g1 : ((1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5)) *
          (1 / ((16 : ℝ) * Q1 / ((4 + t * (Real.sqrt 5 - 1)) ^ 2)) *
            (4 * Real.sqrt (10 + 2 * Real.sqrt 5) /
              ((4 + t * (Real.sqrt 5 - 1)) ^ 2))) =
          (1 / 10 : ℝ) * 4 *
            (Real.sqrt (10 + 2 * Real.sqrt 5) *
              Real.sqrt (10 + 2 * Real.sqrt 5)) / (16 * Q1) := by
        field_simp
      rw [g1, hk1m]
      field_simp
      ring
    have hC : HasDerivAt
        (fun u : ℝ => (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan (u * Real.sqrt (10 + 2 * Real.sqrt 5) /
            (4 + u * (Real.sqrt 5 - 1))))
        ((5 + Real.sqrt 5) /
          (20 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2))) t :=
      hd3 ▸ hC0
    -- Piece D: derivative of the second arctan term.
    have hnum2 : HasDerivAt (fun u : ℝ => u * Real.sqrt (10 - 2 * Real.sqrt 5))
        (Real.sqrt (10 - 2 * Real.sqrt 5)) t := by
      simpa using (hasDerivAt_id t).mul_const (Real.sqrt (10 - 2 * Real.sqrt 5))
    have hden2 : HasDerivAt (fun u : ℝ => 4 - u * (Real.sqrt 5 + 1))
        (-(Real.sqrt 5 + 1)) t := by
      have hlin4 : HasDerivAt (fun u : ℝ => u * (Real.sqrt 5 + 1))
          (Real.sqrt 5 + 1) t := by
        simpa using (hasDerivAt_id t).mul_const (Real.sqrt 5 + 1)
      have hcomb := (hasDerivAt_const t (4 : ℝ)).sub hlin4
      have hmid : HasDerivAt
          ((fun _ : ℝ => (4 : ℝ)) - (fun u : ℝ => u * (Real.sqrt 5 + 1)))
          (-(Real.sqrt 5 + 1)) t := by
        simpa using hcomb
      exact hmid
    have hu2div : HasDerivAt
        (fun u : ℝ => u * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - u * (Real.sqrt 5 + 1)))
        ((Real.sqrt (10 - 2 * Real.sqrt 5) * (4 - t * (Real.sqrt 5 + 1)) -
          t * Real.sqrt (10 - 2 * Real.sqrt 5) * (-(Real.sqrt 5 + 1))) /
          (4 - t * (Real.sqrt 5 + 1)) ^ 2) t :=
      hnum2.div hden2 hd2
    have harctan2 : HasDerivAt
        (fun u : ℝ => Real.arctan (u * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - u * (Real.sqrt 5 + 1))))
        (1 / (1 + (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - t * (Real.sqrt 5 + 1))) ^ 2) *
          ((Real.sqrt (10 - 2 * Real.sqrt 5) * (4 - t * (Real.sqrt 5 + 1)) -
            t * Real.sqrt (10 - 2 * Real.sqrt 5) * (-(Real.sqrt 5 + 1))) /
            (4 - t * (Real.sqrt 5 + 1)) ^ 2)) t :=
      hu2div.arctan
    have hD0 : HasDerivAt
        (fun u : ℝ => (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan (u * Real.sqrt (10 - 2 * Real.sqrt 5) /
            (4 - u * (Real.sqrt 5 + 1))))
        ((1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          (1 / (1 + (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
            (4 - t * (Real.sqrt 5 + 1))) ^ 2) *
            ((Real.sqrt (10 - 2 * Real.sqrt 5) * (4 - t * (Real.sqrt 5 + 1)) -
              t * Real.sqrt (10 - 2 * Real.sqrt 5) * (-(Real.sqrt 5 + 1))) /
              (4 - t * (Real.sqrt 5 + 1)) ^ 2))) t :=
      harctan2.const_mul ((1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5))
    have step1' : (Real.sqrt (10 - 2 * Real.sqrt 5) *
          (4 - t * (Real.sqrt 5 + 1)) -
          t * Real.sqrt (10 - 2 * Real.sqrt 5) * (-(Real.sqrt 5 + 1))) /
          (4 - t * (Real.sqrt 5 + 1)) ^ 2 =
        4 * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - t * (Real.sqrt 5 + 1)) ^ 2 := by
      congr 1
      ring
    have e2' : (4 - t * (Real.sqrt 5 + 1)) ^ 2 +
        t ^ 2 * (10 - 2 * Real.sqrt 5) =
        16 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) := by
      linear_combination t ^ 2 * hs_sq
    have hden_eq' : (1 + (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - t * (Real.sqrt 5 + 1))) ^ 2) * ((4 - t * (Real.sqrt 5 + 1)) ^ 2) =
        16 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) := by
      have eab' : (1 + (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - t * (Real.sqrt 5 + 1))) ^ 2) * ((4 - t * (Real.sqrt 5 + 1)) ^ 2) =
          (4 - t * (Real.sqrt 5 + 1)) ^ 2 +
            t ^ 2 * (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 := by
        have hM' : ((4 : ℝ) - t * (Real.sqrt 5 + 1)) ^ 2 ≠ 0 :=
          pow_ne_zero 2 hd2
        field_simp
      rw [eab', hk2sq]
      exact e2'
    have hu2e : (1 : ℝ) + (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
        (4 - t * (Real.sqrt 5 + 1))) ^ 2 =
        16 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) /
          ((4 - t * (Real.sqrt 5 + 1)) ^ 2) := by
      have hM' : ((4 : ℝ) - t * (Real.sqrt 5 + 1)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 hd2
      rw [eq_div_iff hM']
      exact hden_eq'
    have hd4 : ((1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5)) *
        (1 / (1 + (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
          (4 - t * (Real.sqrt 5 + 1))) ^ 2) *
          ((Real.sqrt (10 - 2 * Real.sqrt 5) * (4 - t * (Real.sqrt 5 + 1)) -
            t * Real.sqrt (10 - 2 * Real.sqrt 5) * (-(Real.sqrt 5 + 1))) /
            (4 - t * (Real.sqrt 5 + 1)) ^ 2)) =
        (5 - Real.sqrt 5) /
          (20 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) := by
      rw [step1', hu2e]
      generalize hQ2e : (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) = Q2
      have hQ2t' : Q2 ≠ 0 := by rw [← hQ2e]; exact hQ2ne
      have hM' : ((4 : ℝ) - t * (Real.sqrt 5 + 1)) ^ 2 ≠ 0 :=
        pow_ne_zero 2 hd2
      have h16' : (16 : ℝ) * Q2 / ((4 - t * (Real.sqrt 5 + 1)) ^ 2) ≠ 0 :=
        div_ne_zero (mul_ne_zero (by norm_num) hQ2t') hM'
      have hk2m : Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.sqrt (10 - 2 * Real.sqrt 5) = 10 - 2 * Real.sqrt 5 := by
        rw [← pow_two]
        exact hk2sq
      have g1' : ((1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5)) *
          (1 / ((16 : ℝ) * Q2 / ((4 - t * (Real.sqrt 5 + 1)) ^ 2)) *
            (4 * Real.sqrt (10 - 2 * Real.sqrt 5) /
              ((4 - t * (Real.sqrt 5 + 1)) ^ 2))) =
          (1 / 10 : ℝ) * 4 *
            (Real.sqrt (10 - 2 * Real.sqrt 5) *
              Real.sqrt (10 - 2 * Real.sqrt 5)) / (16 * Q2) := by
        field_simp
      rw [g1', hk2m]
      field_simp
      ring
    have hD : HasDerivAt
        (fun u : ℝ => (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan (u * Real.sqrt (10 - 2 * Real.sqrt 5) /
            (4 - u * (Real.sqrt 5 + 1))))
        ((5 - Real.sqrt 5) /
          (20 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) t :=
      hd4 ▸ hD0
    -- Assemble the four pieces.
    have hF : HasDerivAt
        (fun t => (1 / 20 : ℝ) * Real.log ((1 + t) ^ 5 / (1 + t ^ 5)) +
          1 / (4 * Real.sqrt 5) *
            Real.log ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
          (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
            Real.arctan (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
              (4 + t * (Real.sqrt 5 - 1))) +
          (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
            Real.arctan (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
              (4 - t * (Real.sqrt 5 + 1))))
        ((1 / 20 : ℝ) * (5 / (1 + t) - 5 * t ^ 4 /
            ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) +
          1 / (4 * Real.sqrt 5) *
            (((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) /
              (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) -
            (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) /
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
          (5 + Real.sqrt 5) /
            (20 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2)) +
          (5 - Real.sqrt 5) /
            (20 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) t :=
      ((hA.add hB).add hC).add hD
    -- The derivative equals the integrand.
    have hDne : (1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
        (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) ≠ 0 :=
      mul_ne_zero (mul_ne_zero h1tne hQ1ne) hQ2ne
    have hder_eq : (1 / 20 : ℝ) * (5 / (1 + t) - 5 * t ^ 4 /
          ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) +
        1 / (4 * Real.sqrt 5) *
          (((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) /
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) -
          (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) /
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
        (5 + Real.sqrt 5) /
          (20 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2)) +
        (5 - Real.sqrt 5) /
          (20 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) =
        1 / (1 + t ^ 5) := by
      rw [hfact t]
      have hsne : Real.sqrt 5 ≠ 0 := ne_of_gt hs_pos
      have e1 : ((1 / 20 : ℝ) * (5 / (1 + t) - 5 * t ^ 4 /
            ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) +
          1 / (4 * Real.sqrt 5) *
            (((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) /
              (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) -
            (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) /
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
          (5 + Real.sqrt 5) /
            (20 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2)) +
          (5 - Real.sqrt 5) /
            (20 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) *
          (Real.sqrt 5 * ((1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) =
          Real.sqrt 5 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) / 4 +
          -Real.sqrt 5 * t ^ 4 / 4 +
          ((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) * (1 + t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) / 4 +
          -(-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) * (1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) / 4 +
          (5 + Real.sqrt 5) * Real.sqrt 5 * (1 + t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) / 20 +
          (5 - Real.sqrt 5) * Real.sqrt 5 * (1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) / 20 := by
        generalize hQ1e : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) = Q1
        generalize hQ2e : (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) = Q2
        have hQ1t' : Q1 ≠ 0 := by rw [← hQ1e]; exact hQ1ne
        have hQ2t' : Q2 ≠ 0 := by rw [← hQ2e]; exact hQ2ne
        have hDne' : (1 + t) * Q1 * Q2 ≠ 0 :=
          mul_ne_zero (mul_ne_zero h1tne hQ1t') hQ2t'
        field_simp
        ring
      have eRHS : (1 / ((1 + t) *
          (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) *
          (Real.sqrt 5 * ((1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) =
          Real.sqrt 5 := by
        generalize hQ1e : (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) = Q1
        generalize hQ2e : (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) = Q2
        have hQ1t' : Q1 ≠ 0 := by rw [← hQ1e]; exact hQ1ne
        have hQ2t' : Q2 ≠ 0 := by rw [← hQ2e]; exact hQ2ne
        have hDne' : (1 + t) * Q1 * Q2 ≠ 0 :=
          mul_ne_zero (mul_ne_zero h1tne hQ1t') hQ2t'
        have hDEN0 : Real.sqrt 5 * ((1 + t) * Q1 * Q2) ≠ 0 :=
          mul_ne_zero hsne hDne'
        field_simp
      have key : Real.sqrt 5 *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) / 4 +
          -Real.sqrt 5 * t ^ 4 / 4 +
          ((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) * (1 + t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) / 4 +
          -(-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) * (1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) / 4 +
          (5 + Real.sqrt 5) * Real.sqrt 5 * (1 + t) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2) / 20 +
          (5 - Real.sqrt 5) * Real.sqrt 5 * (1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) / 20 =
          Real.sqrt 5 := by
        linear_combination
          (Real.sqrt 5 * (-(1 / 20) * t - (9 / 80) * t ^ 2)) * hs_sq
      have hDEN0 : Real.sqrt 5 * ((1 + t) *
          (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
          (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) ≠ 0 :=
        mul_ne_zero hsne hDne
      have hcancel : ((1 / 20 : ℝ) * (5 / (1 + t) - 5 * t ^ 4 /
            ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) +
          1 / (4 * Real.sqrt 5) *
            (((1 / 2 : ℝ) * (Real.sqrt 5 - 1) + 2 * t) /
              (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) -
            (-((1 / 2 : ℝ) * (Real.sqrt 5 + 1)) + 2 * t) /
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
          (5 + Real.sqrt 5) /
            (20 * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2)) +
          (5 - Real.sqrt 5) /
            (20 * (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) *
          (Real.sqrt 5 * ((1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) =
          (1 / ((1 + t) * (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) *
          (Real.sqrt 5 * ((1 + t) *
            (1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) *
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2))) := by
        rw [e1, key]
        exact eRHS.symm
      exact mul_right_cancel₀ hDEN0 hcancel
    have hFt : HasDerivAt
        (fun t => (1 / 20 : ℝ) * Real.log ((1 + t) ^ 5 / (1 + t ^ 5)) +
          1 / (4 * Real.sqrt 5) *
            Real.log ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
              (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
          (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
            Real.arctan (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
              (4 + t * (Real.sqrt 5 - 1))) +
          (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
            Real.arctan (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
              (4 - t * (Real.sqrt 5 + 1))))
        (1 / (1 + t ^ 5)) t :=
      hder_eq ▸ hF
    exact hFt
  have hmain : chapter8Entry14A 5 x =
      (1 / 20 : ℝ) * Real.log ((1 + x) ^ 5 / (1 + x ^ 5)) +
        1 / (4 * Real.sqrt 5) *
          Real.log
            ((1 + (1 / 2 : ℝ) * x * (Real.sqrt 5 - 1) + x ^ 2) /
              (1 - (1 / 2 : ℝ) * x * (Real.sqrt 5 + 1) + x ^ 2)) +
        (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan
            (x * Real.sqrt (10 + 2 * Real.sqrt 5) /
              (4 + x * (Real.sqrt 5 - 1))) +
        (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan
            (x * Real.sqrt (10 - 2 * Real.sqrt 5) /
              (4 - x * (Real.sqrt 5 + 1))) := by
    have hunfold : chapter8Entry14A 5 x =
        (∫ u in (0 : ℝ)..x, 1 / (1 + u ^ (5 : ℕ))) := rfl
    rw [hunfold]
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => (1 / 20 : ℝ) * Real.log ((1 + t) ^ 5 / (1 + t ^ 5)) +
        1 / (4 * Real.sqrt 5) *
          Real.log ((1 + (1 / 2 : ℝ) * t * (Real.sqrt 5 - 1) + t ^ 2) /
            (1 - (1 / 2 : ℝ) * t * (Real.sqrt 5 + 1) + t ^ 2)) +
        (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan (t * Real.sqrt (10 + 2 * Real.sqrt 5) /
            (4 + t * (Real.sqrt 5 - 1))) +
        (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan (t * Real.sqrt (10 - 2 * Real.sqrt 5) /
            (4 - t * (Real.sqrt 5 + 1))))
      (f' := fun u : ℝ => 1 / (1 + u ^ (5 : ℕ))) hderiv hInt
    have hF0' : (1 / 20 : ℝ) * Real.log ((1 + 0) ^ 5 / (1 + 0 ^ 5)) +
        1 / (4 * Real.sqrt 5) *
          Real.log ((1 + (1 / 2 : ℝ) * 0 * (Real.sqrt 5 - 1) + 0 ^ 2) /
            (1 - (1 / 2 : ℝ) * 0 * (Real.sqrt 5 + 1) + 0 ^ 2)) +
        (1 / 10 : ℝ) * Real.sqrt (10 + 2 * Real.sqrt 5) *
          Real.arctan (0 * Real.sqrt (10 + 2 * Real.sqrt 5) /
            (4 + 0 * (Real.sqrt 5 - 1))) +
        (1 / 10 : ℝ) * Real.sqrt (10 - 2 * Real.sqrt 5) *
          Real.arctan (0 * Real.sqrt (10 - 2 * Real.sqrt 5) /
            (4 - 0 * (Real.sqrt 5 + 1))) = 0 := hF0
    rw [hF0', sub_zero] at h
    exact h
  exact ⟨hInt, hL1, hL2, hne1, hne2, hmain⟩

end

end Entry14VIntegral5

end MathlibExt.Analysis.Ramanujan.Part1Ch8
