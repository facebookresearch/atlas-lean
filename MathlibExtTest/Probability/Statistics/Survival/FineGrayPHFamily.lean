/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.FineGrayPHFamily
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.Statistics.FineGray
open MathlibExt.Probability.Statistics.FineGrayPHFamily

namespace MathlibExtTest.Probability.Statistics.FineGrayPHFamily

/-! ### Values computed from the definitions -/

/-- A latent value below `1` is a cause-of-interest failure at time `ω / (1 - ω)`. -/
example : phCause (1 / 2) = true ∧ phTime (1 / 2) = 1 := by
  norm_num [phCause, phTime]

/-- A latent value at least `1` is a competing failure at time `1`. -/
example : phCause 2 = false ∧ phTime 2 = 1 := by
  norm_num [phCause, phTime]

/-- The baseline hazard is not the zero function: `λ₀(0) = 1` and `λ₀(1) = 1 / 4`. -/
example : phBaseline 0 = 1 ∧ phBaseline 1 = 1 / 4 := by
  norm_num [phBaseline]

/-- The cumulative incidence at `t = 1`, computed from the definition of `cif` and the
exponential CDF: `F_c(1; x) = 1 - exp (-exp ⟪β, x⟫ / 2)`. -/
theorem cif_one {p : ℕ} (β x : Fin p → ℝ) :
    cif (phMeasure β x) phTime phCause true 1 = 1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * (1 / 2))) := by
  have hs : {ω : ℝ | phTime ω ≤ 1 ∧ phCause ω = true} = Iic (1 / 2) := by
    ext ω
    simp only [phTime, phCause, decide_eq_true_eq, mem_ofPred_eq, mem_Iic]
    constructor
    · rintro ⟨h, hω⟩
      rw [ite_eq_left hω, div_le_iff₀ (by linarith)] at h
      linarith
    · intro h
      have hω : ω < 1 := by linarith
      refine ⟨?_, hω⟩
      rw [ite_eq_left hω, div_le_iff₀ (by linarith)]
      linarith
  rw [cif, hs, ← cdf_eq_real, phMeasure, cdf_expMeasure_eq (Real.exp_pos _),
    ite_eq_left (by norm_num)]

/-- Non-vacuity: the cause of interest occurs, `F_c(1; x) > 0` (from `cif_one`). -/
example {p : ℕ} (β x : Fin p → ℝ) : 0 < cif (phMeasure β x) phTime phCause true 1 := by
  rw [cif_one, sub_pos]
  have h := Real.exp_lt_exp.2
    (neg_lt_zero.2 (mul_pos (Real.exp_pos (β ⬝ᵥ x)) (by norm_num : (0 : ℝ) < 1 / 2)))
  rwa [Real.exp_zero] at h

/-- Non-vacuity: the cumulative incidence depends on the covariate. With `β = 1` in one dimension,
`F_c(1; 0) = 1 - exp (-1 / 2)` differs from `F_c(1; 1) = 1 - exp (-e / 2)`. -/
example : cif (phMeasure ![1] ![0]) phTime phCause true 1 ≠
    cif (phMeasure ![1] ![1]) phTime phCause true 1 := by
  have d0 : (![1] : Fin 1 → ℝ) ⬝ᵥ ![0] = 0 := by simp [dotProduct]
  have d1 : (![1] : Fin 1 → ℝ) ⬝ᵥ ![1] = 1 := by simp [dotProduct]
  rw [cif_one, cif_one, d0, d1, Real.exp_zero]
  intro h
  have h1 : Real.exp (-(1 * (1 / 2))) = Real.exp (-(Real.exp 1 * (1 / 2))) := by linarith
  have h2 := Real.exp_injective h1
  have h3 : Real.exp 1 = 1 := by linarith
  have h4 := Real.exp_lt_exp.2 (zero_lt_one : (0 : ℝ) < 1)
  rw [Real.exp_zero, h3] at h4
  exact lt_irrefl _ h4

/-- Boundary: `F_c(0; x) = 0`. -/
example {p : ℕ} (β x : Fin p → ℝ) : cif (phMeasure β x) phTime phCause true 0 = 0 := by
  have hs : {ω : ℝ | phTime ω ≤ 0 ∧ phCause ω = true} = Iic 0 := by
    ext ω
    simp only [phTime, phCause, decide_eq_true_eq, mem_ofPred_eq, mem_Iic]
    constructor
    · rintro ⟨h, hω⟩
      rw [ite_eq_left hω, div_le_iff₀ (by linarith)] at h
      linarith
    · intro h
      have hω : ω < 1 := by linarith
      refine ⟨?_, hω⟩
      rw [ite_eq_left hω]
      exact div_nonpos_of_nonpos_of_nonneg h (by linarith)
  rw [cif, hs, ← cdf_eq_real, phMeasure, cdf_expMeasure_eq (Real.exp_pos _),
    ite_eq_left le_rfl]
  simp

/-! ### The proportional subdistribution hazards model -/

/-- The family is a proportional subdistribution hazards model with a positive baseline. -/
example {p : ℕ} (β : Fin p → ℝ) :
    IsPropSubdistHazards (phMeasure β) phTime phCause true phBaseline β ∧
      ∀ t, 0 ≤ t → 0 < phBaseline t :=
  ⟨isPropSubdistHazards_phMeasure β, fun _ ht => phBaseline_pos ht⟩

/-- For `t > -1`, `{T ≤ t, J = true} = {ω ≤ t / (1 + t)}`, computed from the definitions. -/
private lemma setOf_le {t : ℝ} (ht : -1 < t) :
    {ω : ℝ | phTime ω ≤ t ∧ phCause ω = true} = Iic (t / (1 + t)) := by
  have h1 : 0 < 1 + t := by linarith
  ext ω
  simp only [phTime, phCause, decide_eq_true_eq, mem_ofPred_eq, mem_Iic]
  constructor
  · rintro ⟨h, hω⟩
    rw [ite_eq_left hω, div_le_iff₀ (by linarith)] at h
    rw [le_div_iff₀ h1]
    linarith
  · intro h
    have hω : ω < 1 := h.trans_lt ((div_lt_one h1).2 (by linarith))
    refine ⟨?_, hω⟩
    rw [ite_eq_left hω, div_le_iff₀ (by linarith)]
    rw [le_div_iff₀ h1] at h
    linarith

/-- The cumulative incidence on `[0, ∞)` from the definition of `cif` and the exponential CDF. -/
private lemma cif_closed {p : ℕ} (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cif (phMeasure β x) phTime phCause true t =
      1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * (t / (1 + t)))) := by
  rw [cif, setOf_le (by linarith), ← cdf_eq_real, phMeasure, cdf_expMeasure_eq (Real.exp_pos _),
    ite_eq_left (div_nonneg ht (by linarith))]

/-- The limit-defined subdistribution hazard at `t = 1` with `β = log 2`, `x = 1` is `1 / 2`,
computed with `hasSubdistHazardAt_of_hasDerivWithinAt` from the closed form
`F_c(t) = 1 - exp (-2 t / (1 + t))`: its right derivative at `1` is `(2 / 4) e⁻¹` and
`(e⁻¹ / 2) / (1 - (1 - e⁻¹)) = 1 / 2`. -/
example : subdistHazard (phMeasure ![Real.log 2] ![1]) phTime phCause true 1 = 1 / 2 := by
  have d : (![Real.log 2] : Fin 1 → ℝ) ⬝ᵥ ![1] = Real.log 2 := by simp [dotProduct]
  have hθ : Real.exp ((![Real.log 2] : Fin 1 → ℝ) ⬝ᵥ ![1]) = 2 := by
    rw [d, Real.exp_log (by norm_num)]
  have hFg : ∀ u : ℝ, 0 ≤ u → cif (phMeasure ![Real.log 2] ![1]) phTime phCause true u =
      1 - Real.exp (-(2 * (u / (1 + u)))) := fun u hu => by
    rw [cif_closed _ _ hu, hθ]
  have hgd : ∀ u : ℝ, 0 ≤ u → HasDerivAt (fun u : ℝ => 1 - Real.exp (-(2 * (u / (1 + u)))))
      (2 / (1 + u) ^ 2 * Real.exp (-(2 * (u / (1 + u))))) u := by
    intro u hu
    have h1 : 1 + u ≠ 0 := by linarith
    have hq : HasDerivAt (fun u : ℝ => u / (1 + u)) (1 / (1 + u) ^ 2) u := by
      refine ((hasDerivAt_id u).div ((hasDerivAt_id u).const_add 1) h1).congr_deriv ?_
      simp only [id]
      field_simp
      ring
    refine (((hq.const_mul 2).neg).exp.const_sub 1).congr_deriv ?_
    simp only [Pi.neg_apply]
    ring
  have hc : ∀ᶠ s in 𝓝[≥] (1 : ℝ),
      ContinuousAt (cif (phMeasure ![Real.log 2] ![1]) phTime phCause true) s := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : (1 : ℝ) ≤ s)
    refine (hgd s (by linarith)).continuousAt.congr ?_
    filter_upwards [Ioi_mem_nhds (by linarith : (0 : ℝ) < s)] with u hu
    exact (hFg u (le_of_lt hu)).symm
  have hd : HasDerivWithinAt (cif (phMeasure ![Real.log 2] ![1]) phTime phCause true)
      (2 / (1 + 1) ^ 2 * Real.exp (-(2 * (1 / (1 + 1))))) (Ici 1) 1 :=
    (hgd 1 zero_le_one).hasDerivWithinAt.congr (fun s (hs : (1 : ℝ) ≤ s) => hFg s (by linarith))
      (hFg 1 zero_le_one)
  have h := hasSubdistHazardAt_of_hasDerivWithinAt measurable_phTime measurableSet_phCause hc hd
  rw [h.subdistHazard_eq, hFg 1 zero_le_one, sub_sub_cancel]
  have he : Real.exp (-(2 * ((1 : ℝ) / (1 + 1)))) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  norm_num

/-- The competing cause occurs, computed from the exponential CDF:
`P(ω > 1) = 1 - F(1) = exp (-exp ⟪β, x⟫) > 0` and `{ω > 1} ⊆ {J = false}`. -/
example {p : ℕ} (β x : Fin p → ℝ) : 0 < (phMeasure β x).real {ω | phCause ω = false} := by
  have hI : (phMeasure β x).real (Ioi 1) = Real.exp (-(Real.exp (β ⬝ᵥ x) * 1)) := by
    rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real, phMeasure,
      cdf_expMeasure_eq (Real.exp_pos _), ite_eq_left zero_le_one, sub_sub_cancel]
  have hsub : Ioi (1 : ℝ) ⊆ {ω | phCause ω = false} := fun ω (hω : 1 < ω) => by
    simpa [phCause] using hω.le
  calc (0 : ℝ) < Real.exp (-(Real.exp (β ⬝ᵥ x) * 1)) := Real.exp_pos _
    _ = (phMeasure β x).real (Ioi 1) := hI.symm
    _ ≤ (phMeasure β x).real {ω | phCause ω = false} := measureReal_mono hsub

/-! ### `cif_eq` and `cif_eq_rpow` against independent computations -/

/-- The cumulative baseline hazard computed by the fundamental theorem of calculus:
`∫₀ᵗ 1 / (1 + s)² ds = t / (1 + t)`. -/
theorem integral_phBaseline {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, phBaseline s = t / (1 + t) := by
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun u : ℝ => u / (1 + u)) (phBaseline s) s := by
    intro s hs
    rw [uIcc_of_le ht] at hs
    have h1 : 1 + s ≠ 0 := by linarith [hs.1]
    refine ((hasDerivAt_id s).div ((hasDerivAt_id s).const_add 1) h1).congr_deriv ?_
    simp only [id, phBaseline]
    field_simp
    ring
  have hi : IntervalIntegrable phBaseline volume 0 t := by
    refine ContinuousOn.intervalIntegrable fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have h1 : 1 + s ≠ 0 := by linarith [hs.1]
    exact (continuousAt_const.div ((continuousAt_const.add continuousAt_id).pow 2)
      (pow_ne_zero 2 h1)).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp

/-- `cif_eq` applied to the family, with the cumulative baseline evaluated by the fundamental
theorem of calculus, gives `F_c(1; x) = 1 - exp (-exp ⟪β, x⟫ / 2)`, matching `cif_one`. -/
example {p : ℕ} (β x : Fin p → ℝ) :
    cif (phMeasure β x) phTime phCause true 1 = 1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * (1 / 2))) := by
  rw [cif_phMeasure_eq_integral β x zero_le_one, integral_phBaseline zero_le_one]
  norm_num

/-- The baseline form of `cif_eq_rpow` checked independently at `t = 1` from `cif_one`:
`1 - (1 - F_c(1; 0)) ^ exp ⟪β, x⟫ = 1 - exp (-1 / 2) ^ exp ⟪β, x⟫ = F_c(1; x)`. -/
example {p : ℕ} (β x : Fin p → ℝ) :
    1 - (1 - cif (phMeasure β 0) phTime phCause true 1) ^ Real.exp (β ⬝ᵥ x) =
      cif (phMeasure β x) phTime phCause true 1 := by
  rw [cif_one, cif_one, dotProduct_zero, Real.exp_zero, sub_sub_cancel, ← Real.exp_mul]
  congr 2
  ring

/-- `cif_eq_rpow` applied to the family at `t = 1`. -/
example {p : ℕ} (β x : Fin p → ℝ) :
    cif (phMeasure β x) phTime phCause true 1 =
      1 - (1 - cif (phMeasure β 0) phTime phCause true 1) ^ Real.exp (β ⬝ᵥ x) :=
  cif_phMeasure_eq_rpow β x zero_le_one

end MathlibExtTest.Probability.Statistics.FineGrayPHFamily
