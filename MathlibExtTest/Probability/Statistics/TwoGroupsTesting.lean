/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.TwoGroupsTesting

@[expose] public section

open MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.TwoGroupsTesting

namespace MathlibExtTest.Probability.Statistics.TwoGroupsTesting

/-- Non-vacuity witness for `TwoGroupsModel`: half the cases are null with z-values uniform on
`[0, 1]`; non-null z-values are uniform on `[0, 1/2]` (density `2`). -/
noncomputable def M : TwoGroupsModel where
  π₀ := 1 / 2
  f₀ := Set.indicator (Set.Icc 0 1) fun _ => 1
  f₁ := Set.indicator (Set.Icc 0 (1 / 2)) fun _ => 2
  π₀_nonneg := by norm_num
  π₀_le_one := by norm_num
  f₀_nonneg z := Set.indicator_nonneg (fun _ _ => zero_le_one) z
  f₁_nonneg z := Set.indicator_nonneg (fun _ _ => zero_le_two) z
  measurable_f₀ := measurable_const.indicator measurableSet_Icc
  measurable_f₁ := measurable_const.indicator measurableSet_Icc
  integrable_f₀ := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by simp) (by simp))
  integrable_f₁ := (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_const (by simp) (by simp))
  integral_f₀ := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    simp
  integral_f₁ := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    norm_num

/-- In the witness, a z-value in `[0, 1/2]` has local fdr `(1/2) / (1/2 + 1) = 1/3`. -/
example : M.localFdr (1 / 4) = 1 / 3 := by
  norm_num [TwoGroupsModel.localFdr, TwoGroupsModel.mixtureDensity, M, Set.indicator_apply]

/-- A z-value in `(1/2, 1]` can only be null: local fdr `1`. -/
example : M.localFdr (3 / 4) = 1 := by
  norm_num [TwoGroupsModel.localFdr, TwoGroupsModel.mixtureDensity, M, Set.indicator_apply]

/-- Junk value outside the support of `f`: `fdr = 0 / 0 = 0` (a null set for the z-values). -/
example : M.localFdr 2 = 0 := by
  norm_num [TwoGroupsModel.localFdr, TwoGroupsModel.mixtureDensity, M, Set.indicator_apply]

/-- In the witness, `fdr(Z)` is the posterior null probability given `Z`. -/
example : M.jointLaw[{p : Bool × ℝ | p.1 = true}.indicator 1 |
      MeasurableSpace.comap Prod.snd (inferInstance : MeasurableSpace ℝ)]
    =ᵐ[M.jointLaw] fun p => M.localFdr p.2 :=
  M.condExp_null_eq_localFdr

/-- `P(H = 0 | Z ∈ Γ) = Fdr(Γ)` holds in the witness for `Γ = (-∞, 1/2]`. -/
example : (M.jointLaw[{p | p.1 = true} | Prod.snd ⁻¹' Set.Iic (1 / 2)]).toReal =
    M.tailFdr (Set.Iic (1 / 2)) :=
  M.cond_null_eq_tailFdr measurableSet_Iic

/-- The joint law of the witness is a probability measure. -/
example : IsProbabilityMeasure M.jointLaw := inferInstance

/-- Storey's theorem for three i.i.d. tests with `P(H = 0, reject) = 1/10` and
`P(H = 1, reject) = 2/10`: `pFDR = 1/3`. -/
example : positiveFDR (fun b => if b = (true, true) then 1 / 10 else
      if b = (false, true) then 2 / 10 else 7 / 20) 3 = 1 / 3 := by
  rw [positiveFDR_eq _ (fun b => by split_ifs <;> norm_num) (by norm_num)]
  norm_num

/-- With no tests the positive FDR is `0` (empty sums), so `0 < m` is needed. -/
example (q : Bool × Bool → ℝ) : positiveFDR q 0 = 0 := by
  simp [positiveFDR, rejectedSet]

/-- Storey's estimator at `t = 1/2` on the p-values `0.1, 0.6, 0.9`: `2 / (3 · 1/2) = 4/3`. -/
example : storeyPi0 (1 / 2) ![1 / 10, 6 / 10, 9 / 10] = 4 / 3 := by
  have : (Finset.univ.filter fun i : Fin 3 => (1 / 2 : ℝ) < ![1 / 10, 6 / 10, 9 / 10] i) =
      {1, 2} := by
    ext i; fin_cases i <;> norm_num
  rw [storeyPi0, this]
  norm_num

/-- Junk value at the excluded tuning parameter `t = 1`: division by zero gives `0`. -/
example (p : Fin 3 → ℝ) : storeyPi0 1 p = 0 := by simp [storeyPi0]

/-- Conservative bias of `π̂₀`, all-null case: three copies of one uniform p-value. -/
example : (3 : ℝ) / 3 ≤ ∫ ω, storeyPi0 (1 / 2) (fun _ : Fin 3 => ω)
    ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  simpa using le_integral_storeyPi0 (p := fun (_ : Fin 3) ω => ω) (fun _ => measurable_id)
    (H0 := Finset.univ) (fun _ _ =>
      MathlibExt.Probability.Statistics.MultipleTesting.isValidPValue_of_hasLaw_uniform HasLaw.id)
    (by norm_num) (by norm_num)

/-- A nonmonotone pFDR curve: the q-value takes the running minimum to the right. -/
example : qValue (fun s => if s < 1 then 1 / 2 else 1 / 4) 0 ≤ 1 / 4 := by
  have h := ciInf_le (f := fun s : Set.Ici (0 : ℝ) => if (s : ℝ) < 1 then (1 / 2 : ℝ) else 1 / 4)
    ⟨0, by rintro _ ⟨s, rfl⟩; dsimp only; split_ifs <;> norm_num⟩ ⟨1, by norm_num⟩
  simpa [qValue] using h

/-- For a monotone pFDR curve the q-value is the pFDR. -/
example (t : ℝ) : qValue (fun s => max s 0) t = max t 0 :=
  qValue_eq_of_monotone (fun _ _ h => max_le_max h le_rfl) t

end MathlibExtTest.Probability.Statistics.TwoGroupsTesting
