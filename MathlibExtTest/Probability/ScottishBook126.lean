/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ScottishBook126
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# A borderline infinite second moment

On the unit interval, the power with exponent `-1/2` has mean two, while its square
has the logarithmically divergent integral of `1/x`. Centering gives an instance of
Kac's limit theorem.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace MathlibExt.Probability.ScottishBook126Wanted

example :
    Tendsto (fun n : ℕ ↦
      (∫ x in Icc (0 : ℝ) 1, Complex.exp
        (Complex.I * ((x ^ (-(1 / 2) : ℝ) - 2 : ℝ) : ℂ) / (Real.sqrt n : ℂ))) ^ n)
      atTop (𝓝 0) := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Icc]⟩
  let g (x : ℝ) := x ^ (-(1 / 2) : ℝ)
  have hg : Integrable g μ := by
    change IntegrableOn g (Icc 0 1)
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by norm_num)
  have hmean : ∫ x, g x ∂μ = 2 := by
    change (∫ x in Icc (0 : ℝ) 1, x ^ (-(1 / 2) : ℝ)) = 2
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by norm_num))]
    norm_num
  apply khintchine_infinite_variance_limit (fun x ↦ g x - 2) (by dsimp [g]; fun_prop)
    (hg.sub (integrable_const (μ := μ) 2))
  · change (∫ x, (g x - 2) ∂μ) = 0
    rw [integral_sub hg (integrable_const 2), hmean]
    simp
  · change ∫⁻ x, ENNReal.ofReal ((g x - 2) ^ 2) ∂μ = ⊤
    by_contra hfin
    have hs := (lintegral_ofReal_ne_top_iff_integrable (by dsimp [g]; fun_prop)
      (ae_of_all μ fun x ↦ sq_nonneg (g x - 2))).1 hfin
    have hcenter := (memLp_two_iff_integrable_sq (by dsimp [g]; fun_prop)).2 hs
    have hL2 : MemLp g 2 μ := by
      simpa [Pi.add_def] using hcenter.add (memLp_const (2 : ℝ))
    have hg₂ : IntegrableOn (fun x ↦ g x ^ 2) (Ioo 0 1) :=
      (integrableOn_Icc_iff_integrableOn_Ioo).1
        ((memLp_two_iff_integrable_sq (by dsimp [g]; fun_prop)).1 hL2)
    have hinv : IntegrableOn (fun x ↦ x ^ (-1 : ℝ)) (Ioo (0 : ℝ) 1) := by
      refine hg₂.congr_fun (fun x hx ↦ ?_) measurableSet_Ioo
      dsimp only [g]
      rw [← Real.rpow_mul_natCast hx.1.le]
      norm_num
    simpa using (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).1 hinv

end MathlibExt.Probability.ScottishBook126Wanted
