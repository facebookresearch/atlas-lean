/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.BootstrapMaximum

@[expose] public section

open Finset Filter Topology MeasureTheory
open MathlibExt.Probability.Statistics.BootstrapMaximum

namespace MathlibExtTest.Probability.Statistics.BootstrapMaximum

/-- Two data points `0 < 1`: three of the four resampling maps draw the larger point. -/
example : (univ.filter fun I : Fin 2 → Fin 2 =>
    univ.sup' univ_nonempty (fun j => (![0, 1] : Fin 2 → ℝ) (I j)) =
      univ.sup' univ_nonempty (![0, 1] : Fin 2 → ℝ)).card = 3 := by
  have h := card_resample_sup_eq 1 (![0, 1] : Fin 2 → ℝ) (by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)
  simpa using h

/-- With two distinct data points the bootstrap reproduces the maximum with probability
`1 - (1/2)² = 3/4`. -/
example : (((1 + 1 : ℕ) : ℝ) ^ (1 + 1))⁻¹ *
    ((univ.filter fun I : Fin 2 → Fin 2 =>
      univ.sup' univ_nonempty (fun j => (![0, 1] : Fin 2 → ℝ) (I j)) =
        univ.sup' univ_nonempty (![0, 1] : Fin 2 → ℝ)).card : ℝ) = 3 / 4 := by
  rw [bootstrap_prob_max_eq 1 (![0, 1] : Fin 2 → ℝ) (by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all)]
  norm_num

/-- The limiting atom `1 - e⁻¹` is strictly between `1/2` and `1`, so the bootstrap law of
`n (X_(n) - X*_(n))` keeps a non-vanishing atom at `0`. -/
example : 1 / 2 < 1 - Real.exp (-1) ∧ 1 - Real.exp (-1) < 1 := by
  constructor
  · rw [Real.exp_neg]
    have h2 : (2 : ℝ) < Real.exp 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
    have : (Real.exp 1)⁻¹ < 1 / 2 := by
      rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
    linarith
  · linarith [Real.exp_pos (-1)]

/-- The almost sure statement applies to the uniform law on `(0, 1)`. -/
example (n : ℕ) :
    ∀ᵐ x ∂(Measure.pi fun _ : Fin (n + 1) =>
        (volume.restrict (Set.Ioc (0 : ℝ) 1) : Measure ℝ)),
      (((n + 1 : ℕ) : ℝ) ^ (n + 1))⁻¹ *
          ((univ.filter fun I : Fin (n + 1) → Fin (n + 1) =>
            univ.sup' univ_nonempty (fun j => x (I j)) = univ.sup' univ_nonempty x).card : ℝ) =
        1 - (1 - 1 / ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  exact ae_bootstrap_prob_max_eq n _

end MathlibExtTest.Probability.Statistics.BootstrapMaximum
