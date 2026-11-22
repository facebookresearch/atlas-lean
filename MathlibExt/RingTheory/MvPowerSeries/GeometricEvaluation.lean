/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

arnovich/asgard-lean, commit
e5e098d5bce80c3907a6acd4e2beb904309a1709,
`Gimle/Asgard/Streams/AnalyticField.lean`. Authors: arnovich.

MIT License

Copyright (c) 2025 Gimle Labs

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

public import MathlibExt.RingTheory.MvPowerSeries.GeometricTail
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.Ring

/-!
# Evaluation of products and reciprocals under geometric majorants

Absolute convergence permits regrouping the Cauchy product. Evaluating the
formal identity `a⁻¹ * a = 1` then identifies the reciprocal and proves that
the evaluated denominator is nonzero, provided the constant coefficient is
nonzero and both series have convergent majorants at the evaluation point.

References: Sambale, *An invitation to formal power series*, Lemma 2.5(i)
and Section 8, https://arxiv.org/abs/2205.00879v7; Lebl, *Tasty Bits of Several
Complex Variables*, version 3.4, Section 1.2, https://www.jirka.org/scv/scv-3.4.pdf.
These evaluation identities are the standard absolutely convergent Cauchy
product and reciprocal argument; no termwise differentiation is asserted.
-/

@[expose] public section

namespace MvPowerSeries

variable {d : ℕ}

/-- Absolutely convergent coefficient evaluation respects multiplication. -/
theorem geometricSum_mul {a b : MvPowerSeries (Fin d) ℚ}
    {ma mb : GeometricMajorant (Fin d)} {r : Fin d → ℚ≥0}
    (ha : IsMajorized a ma) (hb : IsMajorized b mb)
    (ia : ∀ i, (r i : ℚ) < ma.radius i) (ib : ∀ i, (r i : ℚ) < mb.radius i)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((r i : ℚ) : ℝ)) :
    geometricSum (a * b) x = geometricSum a x * geometricSum b x := by
  have sa := summable_norm_seriesTerm ha ia hx
  have sb := summable_norm_seriesTerm hb ib hx
  unfold geometricSum
  rw [sa.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal sb.of_norm
    (summable_mul_of_summable_norm sa sb)]
  congr 1
  funext n
  rw [seriesTerm, coeff_mul, Rat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  simp only [seriesTerm, Rat.cast_mul]
  rw [← hp]
  have mon : (∏ i, x i ^ (p.1 + p.2) i) =
      (∏ i, x i ^ p.1 i) * ∏ i, x i ^ p.2 i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Finsupp.add_apply, pow_add]
  rw [mon]
  ring

/-- Evaluation commutes with rational scalar multiplication. -/
theorem geometricSum_C_mul (q : ℚ) (a : MvPowerSeries (Fin d) ℚ) (x : Fin d → ℝ) :
    geometricSum (C q * a) x = q * geometricSum a x := by
  unfold geometricSum
  rw [← tsum_mul_left]
  congr 1
  funext n
  simp only [seriesTerm, coeff_C_mul, Rat.cast_mul, mul_assoc]

/-- The unit series evaluates to one. -/
@[simp] theorem geometricSum_one (x : Fin d → ℝ) :
    geometricSum (1 : MvPowerSeries (Fin d) ℚ) x = 1 := by
  unfold geometricSum
  rw [tsum_eq_single 0]
  · simp [seriesTerm]
  · intro n hn
    simp [seriesTerm, coeff_one, hn]

/-- Evaluation of a formal reciprocal; the evaluated denominator cannot vanish. -/
theorem geometricSum_inv {a : MvPowerSeries (Fin d) ℚ}
    {ma mi : GeometricMajorant (Fin d)} {r : Fin d → ℚ≥0}
    (hc : constantCoeff a ≠ 0) (ha : IsMajorized a ma) (hi : IsMajorized a⁻¹ mi)
    (ia : ∀ i, (r i : ℚ) < ma.radius i) (ii : ∀ i, (r i : ℚ) < mi.radius i)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((r i : ℚ) : ℝ)) :
    geometricSum a⁻¹ x = (geometricSum a x)⁻¹ ∧ geometricSum a x ≠ 0 := by
  have one : geometricSum a⁻¹ x * geometricSum a x = 1 := by
    rw [← geometricSum_mul hi ha ii ia hx, MvPowerSeries.inv_mul_cancel a hc, geometricSum_one]
  exact ⟨eq_inv_of_mul_eq_one_left one, right_ne_zero_of_mul_eq_one one⟩

end MvPowerSeries
