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
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14(vii)

Closed form for ∫₀ˣ 1/(1+u⁸) du via arctan and log terms.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry14ViiIntegral8

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)

private lemma quad_pos {s t : ℝ} (hs : s ^ 2 < 4) :
    0 < 1 + t * s + t ^ 2 ∧ 0 < 1 - t * s + t ^ 2 := by
  constructor
  · nlinarith [sq_nonneg (t + s / 2)]
  · nlinarith [sq_nonneg (t - s / 2)]

private lemma block_hasDerivAt (s u : ℝ) (hN : 1 + u * s + u ^ 2 ≠ 0)
    (hD : 1 - u * s + u ^ 2 ≠ 0) (hQ : 1 - u ^ 2 ≠ 0) :
    HasDerivAt
      (fun v => Real.log ((1 + v * s + v ^ 2) / (1 - v * s + v ^ 2)) +
        2 * Real.arctan (v * s / (1 - v ^ 2)))
      (2 * s * (1 - u ^ 2) / ((1 + u * s + u ^ 2) * (1 - u * s + u ^ 2)) +
        2 * (s * (1 + u ^ 2) / ((1 - u ^ 2) ^ 2 + (u * s) ^ 2))) u := by
  have h1 : HasDerivAt (fun u : ℝ => u * s) s u := by
    simpa using (hasDerivAt_id u).mul_const s
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
    simpa using hasDerivAt_pow 2 u
  have hN' : HasDerivAt (fun u : ℝ => 1 + u * s + u ^ 2) (s + 2 * u) u := by
    have h := ((hasDerivAt_const u (1 : ℝ)).add h1).add h2
    have hfun : ((fun _ => (1 : ℝ)) + (fun u => u * s) + (fun u => u ^ 2))
        = (fun u : ℝ => 1 + u * s + u ^ 2) := by
      funext v
      simp [Pi.add_apply]
    have hder : (0 + s) + 2 * u = s + 2 * u := by ring
    rwa [hfun, hder] at h
  have hD' : HasDerivAt (fun u : ℝ => 1 - u * s + u ^ 2) (-s + 2 * u) u := by
    have h := ((hasDerivAt_const u (1 : ℝ)).sub h1).add h2
    have hfun : ((fun _ => (1 : ℝ)) - (fun u => u * s) + (fun u => u ^ 2))
        = (fun u : ℝ => 1 - u * s + u ^ 2) := by
      funext v
      simp [Pi.add_apply, Pi.sub_apply]
    have hder : (0 - s) + 2 * u = -s + 2 * u := by ring
    rwa [hfun, hder] at h
  have hQ' : HasDerivAt (fun u : ℝ => 1 - u ^ 2) (0 - 2 * u) u := by
    have h := (hasDerivAt_const u (1 : ℝ)).sub h2
    have hfun : ((fun _ => (1 : ℝ)) - (fun u : ℝ => u ^ 2))
        = (fun u : ℝ => 1 - u ^ 2) := by
      funext v
      simp [Pi.sub_apply]
    have hder : (0 : ℝ) - 2 * u = 0 - 2 * u := rfl
    rwa [hfun, hder] at h
  have hdiv : HasDerivAt (fun v : ℝ => (1 + v * s + v ^ 2) / (1 - v * s + v ^ 2))
      (((s + 2 * u) * (1 - u * s + u ^ 2) - (1 + u * s + u ^ 2) * (-s + 2 * u)) /
        (1 - u * s + u ^ 2) ^ 2) u := by
    have h := hN'.div hD' hD
    have hfun : ((fun v : ℝ => 1 + v * s + v ^ 2) / (fun v : ℝ => 1 - v * s + v ^ 2))
        = (fun v : ℝ => (1 + v * s + v ^ 2) / (1 - v * s + v ^ 2)) := by
      funext v
      simp [Pi.div_apply]
    rwa [hfun] at h
  have hne : (1 + u * s + u ^ 2) / (1 - u * s + u ^ 2) ≠ 0 :=
    div_ne_zero hN hD
  have hlog := hdiv.log hne
  have hg : HasDerivAt (fun v : ℝ => v * s / (1 - v ^ 2))
      ((s * (1 - u ^ 2) - u * s * (0 - 2 * u)) / (1 - u ^ 2) ^ 2) u := by
    have h := h1.div hQ' hQ
    have hfun : ((fun v : ℝ => v * s) / (fun v : ℝ => 1 - v ^ 2))
        = (fun v : ℝ => v * s / (1 - v ^ 2)) := by
      funext v
      simp [Pi.div_apply]
    rwa [hfun] at h
  have harctan := hg.arctan
  have hadd := hlog.add (HasDerivAt.const_mul 2 harctan)
  have hfun : (fun y : ℝ => Real.log ((1 + y * s + y ^ 2) / (1 - y * s + y ^ 2))) +
        (fun x : ℝ => 2 * Real.arctan (x * s / (1 - x ^ 2)))
      = (fun v : ℝ => Real.log ((1 + v * s + v ^ 2) / (1 - v * s + v ^ 2)) +
          2 * Real.arctan (v * s / (1 - v ^ 2))) := by
    funext v
    simp [Pi.add_apply]
  rw [hfun] at hadd
  have e1 : (((s + 2 * u) * (1 - u * s + u ^ 2) - (1 + u * s + u ^ 2) * (-s + 2 * u)) /
        (1 - u * s + u ^ 2) ^ 2) / ((1 + u * s + u ^ 2) / (1 - u * s + u ^ 2))
      = 2 * s * (1 - u ^ 2) / ((1 + u * s + u ^ 2) * (1 - u * s + u ^ 2)) := by
    have hND : (1 + u * s + u ^ 2) * (1 - u * s + u ^ 2) ≠ 0 :=
      mul_ne_zero hN hD
    have hDD : (1 - u * s + u ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hD
    field_simp
    ring
  have e2 : 1 / (1 + (u * s / (1 - u ^ 2)) ^ 2) *
        ((s * (1 - u ^ 2) - u * s * (0 - 2 * u)) / (1 - u ^ 2) ^ 2)
      = s * (1 + u ^ 2) / ((1 - u ^ 2) ^ 2 + (u * s) ^ 2) := by
    have hQ2 : (1 - u ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hQ
    have h1g : (1 : ℝ) + (u * s / (1 - u ^ 2)) ^ 2 ≠ 0 := by
      have hpos : (0 : ℝ) < 1 + (u * s / (1 - u ^ 2)) ^ 2 := by
        have hsq := sq_nonneg (u * s / (1 - u ^ 2))
        linarith
      exact ne_of_gt hpos
    have hden : (1 - u ^ 2) ^ 2 + (u * s) ^ 2 ≠ 0 := by
      have h1 : (0 : ℝ) < (1 - u ^ 2) ^ 2 := sq_pos_of_ne_zero hQ
      have h2pos : (0 : ℝ) ≤ (u * s) ^ 2 := sq_nonneg _
      have hpos : (0 : ℝ) < (1 - u ^ 2) ^ 2 + (u * s) ^ 2 := by linarith
      exact ne_of_gt hpos
    field_simp
    ring
  rw [e1, e2] at hadd
  exact hadd

/-- **Ramanujan's closed form for $\int_0^x du/(1 + u^8)$ (Chapter 8, Entry 14(vii)).** Put
$s_\pm = \sqrt{2 \pm \sqrt2}$ and, for real $x$,
$R_\pm(x) = \frac{1 + s_\pm x + x^2}{1 - s_\pm x + x^2}$. For every real $x$ with $|x| < 1$, the
function $u \mapsto 1/(1 + u^8)$ is integrable on the interval between $0$ and $x$, $R_+(x) > 0$,
$R_-(x) > 0$, $1 - x^2 \ne 0$, and
$$\int_0^x \frac{du}{1 + u^8} = \frac{s_+}{16} \left( \log R_+(x) +
2 \arctan \frac{s_+ x}{1 - x^2} \right) + \frac{s_-}{16} \left( \log R_-(x) +
2 \arctan \frac{s_- x}{1 - x^2} \right).$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8,
Entry 14(vii), pp. 189–190.
Proves `Wanted` entry `ramanujan_part1_ch8_entry14_vii_integral8`.
-/
theorem ramanujan_part1_ch8_entry14_vii_integral8 (x : ℝ) (hx : |x| < 1) :
    IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (8 : ℕ))) volume 0 x ∧
      0 <
        (1 + x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) /
          (1 - x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) ∧
      0 <
        (1 + x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) /
          (1 - x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) ∧
      1 - x ^ 2 ≠ 0 ∧
      chapter8Entry14A 8 x =
        Real.sqrt (2 + Real.sqrt 2) / 16 *
            (Real.log
                ((1 + x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) /
                  (1 - x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2)) +
              2 * Real.arctan
                (x * Real.sqrt (2 + Real.sqrt 2) / (1 - x ^ 2))) +
          Real.sqrt (2 - Real.sqrt 2) / 16 *
            (Real.log
                ((1 + x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) /
                  (1 - x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2)) +
              2 * Real.arctan
                (x * Real.sqrt (2 - Real.sqrt 2) / (1 - x ^ 2))) := by
  have hr : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hrlt : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hs1sq : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 = 2 + Real.sqrt 2 := by
    apply Real.sq_sqrt
    linarith
  have hs2sq : (Real.sqrt (2 - Real.sqrt 2)) ^ 2 = 2 - Real.sqrt 2 := by
    apply Real.sq_sqrt
    linarith
  have hs1lt : (Real.sqrt (2 + Real.sqrt 2)) ^ 2 < 4 := by
    rw [hs1sq]
    linarith
  have hs2lt : (Real.sqrt (2 - Real.sqrt 2)) ^ 2 < 4 := by
    rw [hs2sq]
    linarith
  have hx2 : x ^ 2 < 1 := by
    have h1 : (0 : ℝ) < 1 - x := by linarith [abs_lt.mp hx]
    have h2 : (0 : ℝ) < 1 + x := by linarith [abs_lt.mp hx]
    nlinarith [mul_pos h1 h2]
  have hQx : (1 : ℝ) - x ^ 2 ≠ 0 := ne_of_gt (by linarith)
  have hN1x : (0 : ℝ) < 1 + x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2 :=
    (quad_pos hs1lt).1
  have hD1x : (0 : ℝ) < 1 - x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2 :=
    (quad_pos hs1lt).2
  have hN2x : (0 : ℝ) < 1 + x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2 :=
    (quad_pos hs2lt).1
  have hD2x : (0 : ℝ) < 1 - x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2 :=
    (quad_pos hs2lt).2
  have hpos1 : 0 < (1 + x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) /
      (1 - x * Real.sqrt (2 + Real.sqrt 2) + x ^ 2) :=
    div_pos hN1x hD1x
  have hpos2 : 0 < (1 + x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) /
      (1 - x * Real.sqrt (2 - Real.sqrt 2) + x ^ 2) :=
    div_pos hN2x hD2x
  have hcont : Continuous (fun u : ℝ => 1 / (1 + u ^ (8 : ℕ))) := by
    have h1 : Continuous (fun u : ℝ => (1 : ℝ) + u ^ (8 : ℕ)) := by fun_prop
    have h2 : ∀ u : ℝ, (1 : ℝ) + u ^ (8 : ℕ) ≠ 0 := by
      intro u
      have hpos : (0 : ℝ) < 1 + u ^ (8 : ℕ) := by
        nlinarith [sq_nonneg ((u ^ 4 : ℝ))]
      exact ne_of_gt hpos
    have h : Continuous ((fun _ => (1 : ℝ)) / (fun u : ℝ => 1 + u ^ (8 : ℕ))) :=
      continuous_const.div h1 h2
    have hfun : ((fun _ => (1 : ℝ)) / (fun u : ℝ => 1 + u ^ (8 : ℕ)))
        = (fun u : ℝ => 1 / (1 + u ^ (8 : ℕ))) := by
      funext v
      simp [Pi.div_apply]
    rwa [hfun] at h
  have hint : IntervalIntegrable (fun u : ℝ => 1 / (1 + u ^ (8 : ℕ))) volume 0 x :=
    hcont.intervalIntegrable 0 x
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) x,
      HasDerivAt
        (fun v => Real.sqrt (2 + Real.sqrt 2) / 16 *
            (Real.log ((1 + v * Real.sqrt (2 + Real.sqrt 2) + v ^ 2) /
              (1 - v * Real.sqrt (2 + Real.sqrt 2) + v ^ 2)) +
              2 * Real.arctan (v * Real.sqrt (2 + Real.sqrt 2) / (1 - v ^ 2))) +
          Real.sqrt (2 - Real.sqrt 2) / 16 *
            (Real.log ((1 + v * Real.sqrt (2 - Real.sqrt 2) + v ^ 2) /
              (1 - v * Real.sqrt (2 - Real.sqrt 2) + v ^ 2)) +
              2 * Real.arctan (v * Real.sqrt (2 - Real.sqrt 2) / (1 - v ^ 2))))
        (1 / (1 + u ^ (8 : ℕ))) u := by
    intro u hu
    have hu1 : |u| < 1 := by
      rw [Set.mem_uIcc] at hu
      rcases hu with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_lt]
        constructor <;> linarith [abs_lt.mp hx]
      · rw [abs_lt]
        constructor <;> linarith [abs_lt.mp hx]
    have hu2 : u ^ 2 < 1 := by
      have h1 : (0 : ℝ) < 1 - u := by linarith [abs_lt.mp hu1]
      have h2 : (0 : ℝ) < 1 + u := by linarith [abs_lt.mp hu1]
      nlinarith [mul_pos h1 h2]
    have hQu : (1 : ℝ) - u ^ 2 ≠ 0 := ne_of_gt (by linarith)
    have hN1 : (1 : ℝ) + u * Real.sqrt (2 + Real.sqrt 2) + u ^ 2 ≠ 0 :=
      ne_of_gt (quad_pos hs1lt).1
    have hD1 : (1 : ℝ) - u * Real.sqrt (2 + Real.sqrt 2) + u ^ 2 ≠ 0 :=
      ne_of_gt (quad_pos hs1lt).2
    have hN2 : (1 : ℝ) + u * Real.sqrt (2 - Real.sqrt 2) + u ^ 2 ≠ 0 :=
      ne_of_gt (quad_pos hs2lt).1
    have hD2 : (1 : ℝ) - u * Real.sqrt (2 - Real.sqrt 2) + u ^ 2 ≠ 0 :=
      ne_of_gt (quad_pos hs2lt).2
    have b1 := block_hasDerivAt (Real.sqrt (2 + Real.sqrt 2)) u hN1 hD1 hQu
    have b2 := block_hasDerivAt (Real.sqrt (2 - Real.sqrt 2)) u hN2 hD2 hQu
    have hF := (HasDerivAt.const_mul (Real.sqrt (2 + Real.sqrt 2) / 16) b1).add
      (HasDerivAt.const_mul (Real.sqrt (2 - Real.sqrt 2) / 16) b2)
    have hfun : (fun y : ℝ => Real.sqrt (2 + Real.sqrt 2) / 16 *
          (Real.log ((1 + y * Real.sqrt (2 + Real.sqrt 2) + y ^ 2) /
            (1 - y * Real.sqrt (2 + Real.sqrt 2) + y ^ 2)) +
            2 * Real.arctan (y * Real.sqrt (2 + Real.sqrt 2) / (1 - y ^ 2)))) +
        (fun y : ℝ => Real.sqrt (2 - Real.sqrt 2) / 16 *
          (Real.log ((1 + y * Real.sqrt (2 - Real.sqrt 2) + y ^ 2) /
            (1 - y * Real.sqrt (2 - Real.sqrt 2) + y ^ 2)) +
            2 * Real.arctan (y * Real.sqrt (2 - Real.sqrt 2) / (1 - y ^ 2))))
        = (fun v : ℝ => Real.sqrt (2 + Real.sqrt 2) / 16 *
            (Real.log ((1 + v * Real.sqrt (2 + Real.sqrt 2) + v ^ 2) /
              (1 - v * Real.sqrt (2 + Real.sqrt 2) + v ^ 2)) +
              2 * Real.arctan (v * Real.sqrt (2 + Real.sqrt 2) / (1 - v ^ 2))) +
          Real.sqrt (2 - Real.sqrt 2) / 16 *
            (Real.log ((1 + v * Real.sqrt (2 - Real.sqrt 2) + v ^ 2) /
              (1 - v * Real.sqrt (2 - Real.sqrt 2) + v ^ 2)) +
              2 * Real.arctan (v * Real.sqrt (2 - Real.sqrt 2) / (1 - v ^ 2)))) := by
      funext v
      simp [Pi.add_apply]
    rw [hfun] at hF
    have hder : Real.sqrt (2 + Real.sqrt 2) / 16 *
          (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2) /
            ((1 + u * Real.sqrt (2 + Real.sqrt 2) + u ^ 2) *
              (1 - u * Real.sqrt (2 + Real.sqrt 2) + u ^ 2)) +
            2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2) /
              ((1 - u ^ 2) ^ 2 + (u * Real.sqrt (2 + Real.sqrt 2)) ^ 2))) +
        Real.sqrt (2 - Real.sqrt 2) / 16 *
          (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2) /
            ((1 + u * Real.sqrt (2 - Real.sqrt 2) + u ^ 2) *
              (1 - u * Real.sqrt (2 - Real.sqrt 2) + u ^ 2)) +
            2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2) /
              ((1 - u ^ 2) ^ 2 + (u * Real.sqrt (2 - Real.sqrt 2)) ^ 2)))
        = 1 / (1 + u ^ (8 : ℕ)) := by
      have hND1 : (1 + u * Real.sqrt (2 + Real.sqrt 2) + u ^ 2) *
          (1 - u * Real.sqrt (2 + Real.sqrt 2) + u ^ 2)
          = 1 - Real.sqrt 2 * u ^ 2 + u ^ 4 := by
        linear_combination (-u ^ 2) * hs1sq
      have hQ1 : (1 - u ^ 2) ^ 2 + (u * Real.sqrt (2 + Real.sqrt 2)) ^ 2
          = 1 + Real.sqrt 2 * u ^ 2 + u ^ 4 := by
        linear_combination (u ^ 2) * hs1sq
      have hND2 : (1 + u * Real.sqrt (2 - Real.sqrt 2) + u ^ 2) *
          (1 - u * Real.sqrt (2 - Real.sqrt 2) + u ^ 2)
          = 1 + Real.sqrt 2 * u ^ 2 + u ^ 4 := by
        linear_combination (-u ^ 2) * hs2sq
      have hQ2 : (1 - u ^ 2) ^ 2 + (u * Real.sqrt (2 - Real.sqrt 2)) ^ 2
          = 1 - Real.sqrt 2 * u ^ 2 + u ^ 4 := by
        linear_combination (u ^ 2) * hs2sq
      have hA : (0 : ℝ) < 1 - Real.sqrt 2 * u ^ 2 + u ^ 4 := by
        nlinarith [sq_nonneg (u ^ 2 - Real.sqrt 2 / 2), hr]
      have hB : (0 : ℝ) < 1 + Real.sqrt 2 * u ^ 2 + u ^ 4 := by
        nlinarith [sq_nonneg (u ^ 2 + Real.sqrt 2 / 2), hr]
      have h8 : (0 : ℝ) < 1 + u ^ (8 : ℕ) := by
        nlinarith [sq_nonneg ((u ^ 4 : ℝ))]
      have hAB : (1 - Real.sqrt 2 * u ^ 2 + u ^ 4) *
          (1 + Real.sqrt 2 * u ^ 2 + u ^ 4) = 1 + u ^ (8 : ℕ) := by
        linear_combination (-u ^ 4) * hr
      have hNc : (2 - Real.sqrt 2 * u ^ 2) * (1 + Real.sqrt 2 * u ^ 2 + u ^ 4) +
          (2 + Real.sqrt 2 * u ^ 2) * (1 - Real.sqrt 2 * u ^ 2 + u ^ 4) = 4 := by
        linear_combination (-2 * u ^ 4) * hr
      have hA' : (1 : ℝ) - Real.sqrt 2 * u ^ 2 + u ^ 4 ≠ 0 := ne_of_gt hA
      have hB' : (1 : ℝ) + Real.sqrt 2 * u ^ 2 + u ^ 4 ≠ 0 := ne_of_gt hB
      have h8' : (1 : ℝ) + u ^ (8 : ℕ) ≠ 0 := ne_of_gt h8
      rw [hND1, hQ1, hND2, hQ2]
      have keyA : Real.sqrt (2 + Real.sqrt 2) *
            (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2)) +
          Real.sqrt (2 - Real.sqrt 2) *
            (2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2)))
          = 4 * (2 - Real.sqrt 2 * u ^ 2) := by
        linear_combination (2 * (1 - u ^ 2)) * hs1sq + (2 * (1 + u ^ 2)) * hs2sq
      have keyB : Real.sqrt (2 + Real.sqrt 2) *
            (2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2))) +
          Real.sqrt (2 - Real.sqrt 2) *
            (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2))
          = 4 * (2 + Real.sqrt 2 * u ^ 2) := by
        linear_combination (2 * (1 + u ^ 2)) * hs1sq + (2 * (1 - u ^ 2)) * hs2sq
      have gA : Real.sqrt (2 + Real.sqrt 2) / 16 *
            (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2) /
              (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)) +
          Real.sqrt (2 - Real.sqrt 2) / 16 *
            (2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2) /
              (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)))
          = ((2 - Real.sqrt 2 * u ^ 2) / 4) /
            (1 - Real.sqrt 2 * u ^ 2 + u ^ 4) := by
        have eA : Real.sqrt (2 + Real.sqrt 2) / 16 *
              (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2) /
                (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)) +
            Real.sqrt (2 - Real.sqrt 2) / 16 *
              (2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2) /
                (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)))
            = (Real.sqrt (2 + Real.sqrt 2) *
                (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2)) +
              Real.sqrt (2 - Real.sqrt 2) *
                (2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2)))) /
              (16 * (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)) := by
          field_simp
        have eA' : ((2 - Real.sqrt 2 * u ^ 2) / 4) /
              (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)
            = (4 * (2 - Real.sqrt 2 * u ^ 2)) /
              (16 * (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)) := by
          field_simp
          ring
        rw [eA, eA', keyA]
      have gB : Real.sqrt (2 + Real.sqrt 2) / 16 *
            (2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2) /
              (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))) +
          Real.sqrt (2 - Real.sqrt 2) / 16 *
            (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2) /
              (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))
          = ((2 + Real.sqrt 2 * u ^ 2) / 4) /
            (1 + Real.sqrt 2 * u ^ 2 + u ^ 4) := by
        have eB : Real.sqrt (2 + Real.sqrt 2) / 16 *
              (2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2) /
                (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))) +
            Real.sqrt (2 - Real.sqrt 2) / 16 *
              (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2) /
                (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))
            = (Real.sqrt (2 + Real.sqrt 2) *
                (2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2))) +
              Real.sqrt (2 - Real.sqrt 2) *
                (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2))) /
              (16 * (1 + Real.sqrt 2 * u ^ 2 + u ^ 4)) := by
          field_simp
        have eB' : ((2 + Real.sqrt 2 * u ^ 2) / 4) /
              (1 + Real.sqrt 2 * u ^ 2 + u ^ 4)
            = (4 * (2 + Real.sqrt 2 * u ^ 2)) /
              (16 * (1 + Real.sqrt 2 * u ^ 2 + u ^ 4)) := by
          field_simp
          ring
        rw [eB, eB', keyB]
      have hrw : Real.sqrt (2 + Real.sqrt 2) / 16 *
            (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2) /
              (1 - Real.sqrt 2 * u ^ 2 + u ^ 4) +
              2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2) /
                (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))) +
          Real.sqrt (2 - Real.sqrt 2) / 16 *
            (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2) /
              (1 + Real.sqrt 2 * u ^ 2 + u ^ 4) +
              2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2) /
                (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)))
          = (Real.sqrt (2 + Real.sqrt 2) / 16 *
              (2 * Real.sqrt (2 + Real.sqrt 2) * (1 - u ^ 2) /
                (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)) +
            Real.sqrt (2 - Real.sqrt 2) / 16 *
              (2 * (Real.sqrt (2 - Real.sqrt 2) * (1 + u ^ 2) /
                (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)))) +
            (Real.sqrt (2 + Real.sqrt 2) / 16 *
              (2 * (Real.sqrt (2 + Real.sqrt 2) * (1 + u ^ 2) /
                (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))) +
            Real.sqrt (2 - Real.sqrt 2) / 16 *
              (2 * Real.sqrt (2 - Real.sqrt 2) * (1 - u ^ 2) /
                (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))) := by
        field_simp
        ring
      rw [hrw, gA, gB]
      have e : ((2 - Real.sqrt 2 * u ^ 2) / 4) /
            (1 - Real.sqrt 2 * u ^ 2 + u ^ 4) +
          ((2 + Real.sqrt 2 * u ^ 2) / 4) / (1 + Real.sqrt 2 * u ^ 2 + u ^ 4)
          = ((2 - Real.sqrt 2 * u ^ 2) * (1 + Real.sqrt 2 * u ^ 2 + u ^ 4) +
            (2 + Real.sqrt 2 * u ^ 2) * (1 - Real.sqrt 2 * u ^ 2 + u ^ 4)) /
            (4 * ((1 - Real.sqrt 2 * u ^ 2 + u ^ 4) *
              (1 + Real.sqrt 2 * u ^ 2 + u ^ 4))) := by
        field_simp
      rw [e, hNc, hAB]
      have hfin : (4 : ℝ) / (4 * (1 + u ^ (8 : ℕ))) = 1 / (1 + u ^ (8 : ℕ)) := by
        field_simp
      exact hfin
    rwa [hder] at hF
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hderiv u hu) hint
  have hF0 : Real.sqrt (2 + Real.sqrt 2) / 16 *
        (Real.log ((1 + 0 * Real.sqrt (2 + Real.sqrt 2) + 0 ^ 2) /
          (1 - 0 * Real.sqrt (2 + Real.sqrt 2) + 0 ^ 2)) +
          2 * Real.arctan (0 * Real.sqrt (2 + Real.sqrt 2) / (1 - 0 ^ 2))) +
      Real.sqrt (2 - Real.sqrt 2) / 16 *
        (Real.log ((1 + 0 * Real.sqrt (2 - Real.sqrt 2) + 0 ^ 2) /
          (1 - 0 * Real.sqrt (2 - Real.sqrt 2) + 0 ^ 2)) +
          2 * Real.arctan (0 * Real.sqrt (2 - Real.sqrt 2) / (1 - 0 ^ 2)))
      = 0 := by
    simp
  rw [hF0, sub_zero] at hFTC
  refine ⟨hint, hpos1, hpos2, hQx, ?_⟩
  unfold chapter8Entry14A
  exact hFTC

end

end Entry14ViiIntegral8

end MathlibExt.Analysis.Ramanujan.Part1Ch8
