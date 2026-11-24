/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Coalescent.LambdaCoalescent
public import MathlibExt.Probability.Distributions.BetaMoments

/-!
# Beta-coalescent merger rates

The `Beta(2 - α, α)` law on `[0, 1]` is Mathlib's `betaMeasure (2 - α) α` pushed to the unit
interval; the density is carried by `(0, 1)`, so the clamp changes nothing. For `0 < α < 2` it
is a probability measure and Pitman's rates are
`λ_{b,k} = B(k - α, b - k + α) / B(2 - α, α)`. At `α = 1` this is the Bolthausen–Sznitman
coalescent.

## References

* J. Pitman, "Coalescents with multiple collisions", *Annals of Probability* 27 (1999),
  1870–1902.
* J. Berestycki, N. Berestycki and J. Schweinsberg, "Beta-coalescents and continuous stable
  random trees", *Annals of Probability* 35 (2007), eq. (1).
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent

open MeasureTheory ProbabilityTheory unitInterval LambdaCoalescent

/-- The `Beta(2 - α, α)` law as a measure on `[0, 1]`. It is a probability measure for
`0 < α < 2`; for other `α` the density is evaluated as written (`Γ` is `0` at its poles,
`1 / 0 = 0`, negative values read as `0`) and need not give a probability measure (`α = 2` gives
the zero measure). -/
noncomputable def betaLambda (α : ℝ) : Measure I :=
  (betaMeasure (2 - α) α).map (Set.projIcc (0 : ℝ) 1 zero_le_one : ℝ → I)

/-- For `0 < α < 2`, `Beta(2 - α, α)` is a probability measure on `[0, 1]` (it has mass one). -/
theorem isProbabilityMeasure_betaLambda {α : ℝ} (h0 : 0 < α) (h2 : α < 2) :
    IsProbabilityMeasure (betaLambda α) := by
  have := isProbabilityMeasureBeta (by linarith : (0 : ℝ) < 2 - α) h0
  unfold betaLambda
  exact (Measure.isProbabilityMeasure_map_iff continuous_projIcc.measurable.aemeasurable).2
    inferInstance

/-- **Closed form of the Beta-coalescent rates**: for `0 < α < 2` and `2 ≤ k ≤ b`,
`λ_{b,k} = B(k - α, b - k + α) / B(2 - α, α)`. The finiteness instance always holds, as
`betaLambda α` is a probability measure for `0 < α < 2`. -/
theorem mergerRate_betaLambda {α : ℝ} (h0 : 0 < α) (h2 : α < 2) [IsFiniteMeasure (betaLambda α)]
    {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    mergerRate (betaLambda α) b k = beta ((k : ℝ) - α) ((b : ℝ) - k + α) / beta (2 - α) α := by
  have ha : (0 : ℝ) < 2 - α := by linarith
  have hproj : Measurable (Set.projIcc (0 : ℝ) 1 zero_le_one : ℝ → I) :=
    continuous_projIcc.measurable
  have hcont : Continuous fun x : I => (x : ℝ) ^ (k - 2) * (1 - (x : ℝ)) ^ (b - k) := by
    fun_prop
  rw [mergerRate_of_le _ hk hkb, betaLambda, integral_map hproj.aemeasurable
    hcont.aestronglyMeasurable]
  have key : ∫ x, ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ) ^ (k - 2) *
        (1 - ((Set.projIcc (0 : ℝ) 1 zero_le_one x : I) : ℝ)) ^ (b - k) ∂betaMeasure (2 - α) α =
      ∫ x, x ^ (k - 2) * (1 - x) ^ (b - k) ∂betaMeasure (2 - α) α := by
    rw [integral_betaMeasure ha h0, integral_betaMeasure ha h0]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    by_cases hx : 0 < x ∧ x < 1
    · simp [Set.projIcc_of_mem _ ⟨hx.1.le, hx.2.le⟩]
    · simp [betaPDFReal, hx]
  rw [key, integral_pow_mul_one_sub_pow_betaMeasure ha h0, Nat.cast_sub hk, Nat.cast_sub hkb]
  congr 2 <;> push_cast <;> ring

/-- At `α = 1` the rates are those of the uniform `Λ` (Atlas `mergerRate_volume`). The finiteness
instance always holds, as `betaLambda 1` is a probability measure. -/
theorem mergerRate_betaLambda_one [IsFiniteMeasure (betaLambda 1)] {b k : ℕ} (hk : 2 ≤ k)
    (hkb : k ≤ b) : mergerRate (betaLambda 1) b k = mergerRate volume b k := by
  rw [mergerRate_betaLambda one_pos one_lt_two hk hkb, mergerRate_volume hk hkb]
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, b = i + 2 + j := ⟨b - (i + 2), by omega⟩
  have hB11 : beta (2 - 1) 1 = 1 := by norm_num [beta, Real.Gamma_one, Real.Gamma_two]
  have e1 : ((i + 2 : ℕ) : ℝ) - 1 = (i : ℝ) + 1 := by push_cast; ring
  have e2 : ((i + 2 + j : ℕ) : ℝ) - ((i + 2 : ℕ) : ℝ) + 1 = (j : ℝ) + 1 := by push_cast; ring
  have e3 : ((i : ℝ) + 1) + ((j : ℝ) + 1) = ((i + j + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
  rw [hB11, div_one, e1, e2, beta, e3, Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, show i + 2 - 2 = i by omega, show i + 2 + j - (i + 2) = j by omega,
    show i + 2 + j - 1 = i + j + 1 by omega]

/-- `Beta(1, 1)` is the uniform measure: the `α = 1` Beta-coalescent is the
Bolthausen–Sznitman coalescent. -/
theorem betaLambda_one : betaLambda 1 = volume := by
  have := isProbabilityMeasure_betaLambda (α := 1) one_pos one_lt_two
  exact eq_of_mergerRate_eq _ _ fun k hk => mergerRate_betaLambda_one hk le_rfl

/-- **Consistency inherited from `mergerRate_consistent`**: for `0 < α < 2` and `2 ≤ k ≤ b`,
the closed form satisfies Pitman's consistency relation `λ_{b,k} = λ_{b+1,k} + λ_{b+1,k+1}`. -/
theorem beta_consistent {α : ℝ} (h0 : 0 < α) (h2 : α < 2) {b k : ℕ} (hk : 2 ≤ k) (hkb : k ≤ b) :
    beta ((k : ℝ) - α) ((b : ℝ) - k + α) =
      beta ((k : ℝ) - α) (((b + 1 : ℕ) : ℝ) - k + α) +
        beta (((k + 1 : ℕ) : ℝ) - α) (((b + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) + α) := by
  have := isProbabilityMeasure_betaLambda h0 h2
  have h := mergerRate_consistent (betaLambda α) hk hkb
  rw [mergerRate_betaLambda h0 h2 hk hkb, mergerRate_betaLambda h0 h2 hk (by omega),
    mergerRate_betaLambda h0 h2 (by omega) (by omega), ← add_div,
    div_left_inj' (beta_pos (by linarith : (0 : ℝ) < 2 - α) h0).ne'] at h
  exact h

end MathlibExt.Biology.PopulationGenetics.Coalescent.BetaCoalescent
