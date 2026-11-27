/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.GeneralizationBounds.TwoLayerAPriori
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory CSLibExt.MachineLearning.GeneralizationBounds

namespace CSLibExtTest.MachineLearning.GeneralizationBounds.TwoLayerAPriori

-- The zero target has an admissible representation with second moment zero.
example :
    ∃ C : ℝ, 0 < C ∧ ∀ {n m : ℕ}, 0 < n → 0 < m →
      ∀ (ρ : Measure (Fin 2 → ℝ)), IsProbabilityMeasure ρ →
      ρ (Set.univ.pi fun _ => Set.Icc (-1 : ℝ) 1)ᶜ = 0 →
      ∀ (lam δ : ℝ), 4 * √(2 * Real.log 4 / n) ≤ lam → 0 < δ →
      1 - ENNReal.ofReal δ ≤ (Measure.pi fun _ : Fin n => ρ)
        {S | ∀ (b : Fin m → ℝ) (w : Fin m → Fin 2 → ℝ),
          (∀ (b' : Fin m → ℝ) (w' : Fin m → Fin 2 → ℝ),
            (n : ℝ)⁻¹ * ∑ i, (max (min (twoLayerReLU b w (S i)) 1) 0) ^ 2 / 2 +
                lam * (pathNorm b w + 1) ≤
              (n : ℝ)⁻¹ * ∑ i, (max (min (twoLayerReLU b' w' (S i)) 1) 0) ^ 2 / 2 +
                lam * (pathNorm b' w' + 1)) →
          ∫⁻ x, ENNReal.ofReal ((max (min (twoLayerReLU b w x) 1) 0) ^ 2) ∂ρ ≤
            ENNReal.ofReal (C * (lam + (1 + √(Real.log (n / δ))) / √(n : ℝ)))} := by
  obtain ⟨C, hC, h⟩ := twoLayer_a_priori_estimate
  refine ⟨C, hC, ?_⟩
  intro n m hn hm ρ hρ hcube lam δ hlam hδ
  let e : Fin 2 → ℝ := fun j => if j = 0 then 1 else 0
  have hsphere : ∀ᵐ w ∂(Measure.dirac e), ∑ j, |w j| = 1 := by
    have hmeas : Measurable fun w : Fin 2 → ℝ => ∑ j, |w j| := by fun_prop
    exact (ae_dirac_iff (hmeas (measurableSet_singleton 1))).2 (by
      simp [e, Fin.sum_univ_two])
  have hd : 1 ≤ Real.log (2 * ((2 : ℕ) : ℝ)) :=
    (Real.le_log_iff_exp_le (by norm_num)).2 (Real.exp_one_lt_three.le.trans (by norm_num))
  have hb := h 2 n m hd hn hm ρ hρ hcube 0 measurable_const
    (by simp) (Measure.dirac e) inferInstance hsphere 0 (by simp) 0 (by simp) (by simp)
    lam δ (by convert hlam using 2; norm_num) hδ
  simpa [Pi.zero_apply] using hb

end CSLibExtTest.MachineLearning.GeneralizationBounds.TwoLayerAPriori
