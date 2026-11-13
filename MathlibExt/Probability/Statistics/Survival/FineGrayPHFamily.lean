/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential
public import MathlibExt.Probability.Statistics.Survival.FineGray

/-!
# A nontrivial proportional subdistribution hazards family

This file constructs an explicit competing-risks model that satisfies the Fine–Gray proportional
subdistribution hazards model `IsPropSubdistHazards` with a strictly positive baseline hazard and
a cause of interest that occurs with positive probability, and it applies the CIF regression
theorems `IsPropSubdistHazards.cif_eq` and `IsPropSubdistHazards.cif_eq_rpow` to it.

## The model

The sample space is `ℝ` with a latent variable `ω`. Given the covariate vector `x`, `ω` has the
exponential law with rate `θ(x) = exp ⟪β, x⟫` (`phMeasure`). A subject with `ω < 1` fails from the
cause of interest (`phCause ω = true`) at time `T = ω / (1 - ω)`; a subject with `ω ≥ 1` fails
from the competing cause (`phCause ω = false`) at time `T = 1` (`phTime`). Then for `t ≥ 0`,

  `F_c(t; x) = P(ω ≤ t / (1 + t)) = 1 - exp (-θ(x) t / (1 + t))`,

so the cumulative baseline subdistribution hazard is `Λ₀(t) = t / (1 + t)` and the baseline
hazard is `λ₀(t) = 1 / (1 + t)²` (`phBaseline`). The cause of interest has total probability
`1 - exp (-θ(x)) < 1`; the competing cause has probability `exp (-θ(x)) > 0`.

## Main results

* `hasSubdistHazardAt_phMeasure`, `isPropSubdistHazards_phMeasure`: the subdistribution hazard,
  computed from the limit definition through `hasSubdistHazardAt_of_hasDerivWithinAt`, is
  `λ₀(t) exp ⟪β, x⟫` at every `t ≥ 0`.
* `phBaseline_pos`, `cif_phMeasure_pos`, `measureReal_competing_pos`: the baseline hazard is
  positive, the cause of interest occurs, and the competing cause occurs.
* `cif_phMeasure_eq_integral`: `IsPropSubdistHazards.cif_eq` applied to the family,
  `F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ ∫₀ᵗ λ₀)`.
* `cif_phMeasure_eq_rpow`: `IsPropSubdistHazards.cif_eq_rpow` applied to the family,
  `F_c(t; x) = 1 - (1 - F_c(t; 0)) ^ exp ⟪β, x⟫`.

## Source receipt

* Model: J. P. Fine and R. J. Gray, *A proportional hazards model for the subdistribution of a
  competing risk*, J. Amer. Statist. Assoc. 94 (1999), 496–509, Section 2 (proportional
  subdistribution hazards and the CIF regression `F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ Λ₀(t))`).
* Reused (not reproved): `IsPropSubdistHazards`, `hasSubdistHazardAt_of_hasDerivWithinAt`,
  `IsPropSubdistHazards.cif_eq`, `IsPropSubdistHazards.cif_eq_rpow` from
  `MathlibExt.Probability.Statistics.Survival.FineGray`; `expMeasure`,
  `isProbabilityMeasure_expMeasure`, `cdf_expMeasure_eq` from Mathlib.
* Proved here: the closed form of `F_c` for the family, its continuity and derivative, the
  subdistribution hazard, and the discharge of every hypothesis of `cif_eq` and `cif_eq_rpow`.
  This family is a nontrivial witness, complementing the zero-baseline witness in the `FineGray`
  tests, whose cause never occurs.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.FineGrayPHFamily

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.Statistics.FineGray

variable {p : ℕ}

/-- The law of the latent variable given the covariate `x`: exponential with rate
`exp ⟪β, x⟫`. -/
noncomputable def phMeasure (β x : Fin p → ℝ) : Measure ℝ :=
  expMeasure (Real.exp (β ⬝ᵥ x))

instance (β x : Fin p → ℝ) : IsProbabilityMeasure (phMeasure β x) :=
  isProbabilityMeasure_expMeasure (Real.exp_pos _)

/-- The failure time: `ω / (1 - ω)` for a cause-of-interest failure (`ω < 1`), and `1` for a
competing failure (`ω ≥ 1`). -/
noncomputable def phTime (ω : ℝ) : ℝ :=
  if ω < 1 then ω / (1 - ω) else 1

/-- The failure cause: `true` (the cause of interest) when `ω < 1`, `false` (the competing cause)
otherwise. -/
noncomputable def phCause (ω : ℝ) : Bool :=
  decide (ω < 1)

/-- The baseline subdistribution hazard `λ₀(t) = 1 / (1 + t)²`. -/
noncomputable def phBaseline (t : ℝ) : ℝ :=
  1 / (1 + t) ^ 2

/-- The failure time is measurable. -/
theorem measurable_phTime : Measurable phTime :=
  Measurable.ite measurableSet_Iio (measurable_id.div (measurable_const.sub measurable_id))
    measurable_const

/-- The cause-of-interest event `{phCause = true}` is `{ω < 1}`. -/
theorem setOf_phCause_eq_true : {ω : ℝ | phCause ω = true} = Iio 1 := by
  ext ω
  simp [phCause]

/-- The cause-of-interest event is measurable. -/
theorem measurableSet_phCause : MeasurableSet {ω : ℝ | phCause ω = true} := by
  rw [setOf_phCause_eq_true]
  exact measurableSet_Iio

/-- For `t > -1`, `{T ≤ t, J = true} = {ω ≤ t / (1 + t)}`. -/
theorem setOf_phTime_le {t : ℝ} (ht : -1 < t) :
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

/-- **The cumulative incidence of the cause of interest** for `t > -1`:
`F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ max (t / (1 + t)) 0)`. -/
theorem cif_phMeasure (β x : Fin p → ℝ) {t : ℝ} (ht : -1 < t) :
    cif (phMeasure β x) phTime phCause true t =
      1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * max (t / (1 + t)) 0)) := by
  rw [cif, setOf_phTime_le ht, ← cdf_eq_real, phMeasure, cdf_expMeasure_eq (Real.exp_pos _)]
  split_ifs with h
  · rw [max_eq_left h]
  · rw [max_eq_right (not_le.1 h).le, mul_zero, neg_zero, Real.exp_zero, sub_self]

/-- **The cumulative incidence of the cause of interest** for `t ≥ 0`:
`F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ t / (1 + t))`. -/
theorem cif_phMeasure_of_nonneg (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cif (phMeasure β x) phTime phCause true t =
      1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * (t / (1 + t)))) := by
  rw [cif_phMeasure β x (by linarith), max_eq_left (div_nonneg ht (by linarith))]

/-- The closed form `1 - exp (-θ t / (1 + t))` of the cumulative incidence on `t ≥ 0`. -/
noncomputable def phCif (θ t : ℝ) : ℝ :=
  1 - Real.exp (-(θ * (t / (1 + t))))

/-- The derivative `θ / (1 + t)² exp (-θ t / (1 + t))` of `phCif θ`. -/
noncomputable def phCifDeriv (θ t : ℝ) : ℝ :=
  θ / (1 + t) ^ 2 * Real.exp (-(θ * (t / (1 + t))))

/-- `phCif θ` has derivative `phCifDeriv θ` away from `t = -1`. -/
theorem hasDerivAt_phCif (θ : ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    HasDerivAt (phCif θ) (phCifDeriv θ t) t := by
  have hq : HasDerivAt (fun u : ℝ => u / (1 + u)) (1 / (1 + t) ^ 2) t := by
    have := (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) ht
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have := (((hq.const_mul θ).neg).exp).const_sub 1
  refine this.congr_deriv ?_
  simp only [phCifDeriv, Pi.neg_apply]
  ring

/-- `phCifDeriv θ` is continuous away from `t = -1`. -/
theorem continuousAt_phCifDeriv (θ : ℝ) {t : ℝ} (ht : 1 + t ≠ 0) :
    ContinuousAt (phCifDeriv θ) t := by
  have h1 : ContinuousAt (fun u : ℝ => 1 + u) t := continuousAt_const.add continuousAt_id
  have hq : ContinuousAt (fun u : ℝ => u / (1 + u)) t := continuousAt_id.div h1 ht
  exact (continuousAt_const.div (h1.pow 2) (pow_ne_zero 2 ht)).mul
    ((continuousAt_const.mul hq).neg.rexp)

/-- The cumulative incidence agrees with `phCif` on `[0, ∞)`. -/
theorem cif_phMeasure_eq_phCif (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cif (phMeasure β x) phTime phCause true t = phCif (Real.exp (β ⬝ᵥ x)) t :=
  cif_phMeasure_of_nonneg β x ht

/-- The cumulative incidence is continuous at every `t > -1`. -/
theorem continuousAt_cif_phMeasure (β x : Fin p → ℝ) {t : ℝ} (ht : -1 < t) :
    ContinuousAt (cif (phMeasure β x) phTime phCause true) t := by
  have h1 : ContinuousAt (fun u : ℝ => 1 + u) t := continuousAt_const.add continuousAt_id
  have hq : ContinuousAt (fun u : ℝ => u / (1 + u)) t :=
    continuousAt_id.div h1 (by linarith)
  have hg : ContinuousAt
      (fun u : ℝ => 1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * max (u / (1 + u)) 0))) t :=
    continuousAt_const.sub ((continuousAt_const.mul (hq.max continuousAt_const)).neg.rexp)
  refine hg.congr ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact (cif_phMeasure β x hu).symm

/-- On `(0, ∞)` the cumulative incidence has derivative `phCifDeriv`. -/
theorem hasDerivAt_cif_phMeasure (β x : Fin p → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cif (phMeasure β x) phTime phCause true)
      (phCifDeriv (Real.exp (β ⬝ᵥ x)) t) t := by
  refine (hasDerivAt_phCif _ (by linarith)).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with u hu
  exact cif_phMeasure_eq_phCif β x (le_of_lt hu)

/-- **The subdistribution hazard of the family** (computed from the limit definition): at every
`t ≥ 0` it is `λ₀(t) exp ⟪β, x⟫ = exp ⟪β, x⟫ / (1 + t)²`. -/
theorem hasSubdistHazardAt_phMeasure (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasSubdistHazardAt (phMeasure β x) phTime phCause true t
      (phBaseline t * Real.exp (β ⬝ᵥ x)) := by
  set θ := Real.exp (β ⬝ᵥ x) with hθ
  have hc : ∀ᶠ s in 𝓝[≥] t, ContinuousAt (cif (phMeasure β x) phTime phCause true) s := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : t ≤ s)
    exact continuousAt_cif_phMeasure β x (by linarith)
  have hd : HasDerivWithinAt (cif (phMeasure β x) phTime phCause true) (phCifDeriv θ t)
      (Ici t) t :=
    ((hasDerivAt_phCif θ (by linarith)).hasDerivWithinAt).congr
      (fun s (hs : t ≤ s) => cif_phMeasure_eq_phCif β x (ht.trans hs))
      (cif_phMeasure_eq_phCif β x ht)
  have h := hasSubdistHazardAt_of_hasDerivWithinAt measurable_phTime measurableSet_phCause hc hd
  convert h using 1
  rw [cif_phMeasure_eq_phCif β x ht, phCif, phCifDeriv, phBaseline, sub_sub_cancel]
  have h1 : (1 + t) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  have h2 : Real.exp (-(θ * (t / (1 + t)))) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  rw [hθ]

/-- **The family satisfies the proportional subdistribution hazards model** with baseline hazard
`λ₀(t) = 1 / (1 + t)²` and regression coefficient `β`. -/
theorem isPropSubdistHazards_phMeasure (β : Fin p → ℝ) :
    IsPropSubdistHazards (phMeasure β) phTime phCause true phBaseline β :=
  fun x _ ht => hasSubdistHazardAt_phMeasure β x ht

/-- The baseline hazard is strictly positive on `[0, ∞)`. -/
theorem phBaseline_pos {t : ℝ} (ht : 0 ≤ t) : 0 < phBaseline t := by
  unfold phBaseline
  have : 0 < 1 + t := by linarith
  positivity

/-- **The cause of interest occurs**: `F_c(t; x) > 0` for every `t > 0`. -/
theorem cif_phMeasure_pos (β x : Fin p → ℝ) {t : ℝ} (ht : 0 < t) :
    0 < cif (phMeasure β x) phTime phCause true t := by
  rw [cif_phMeasure_of_nonneg β x ht.le, sub_pos]
  have h1 : 0 < 1 + t := by linarith
  have h2 : 0 < Real.exp (β ⬝ᵥ x) * (t / (1 + t)) := mul_pos (Real.exp_pos _) (div_pos ht h1)
  have h3 := Real.exp_lt_exp.2 (neg_lt_zero.2 h2)
  rwa [Real.exp_zero] at h3

/-- **The competing cause occurs**: `P(J = false) ≥ exp (-exp ⟪β, x⟫) > 0`. -/
theorem measureReal_competing_pos (β x : Fin p → ℝ) :
    0 < (phMeasure β x).real {ω | phCause ω = false} := by
  have hs : {ω : ℝ | phCause ω = false} = (Iio 1)ᶜ := by
    ext ω
    simp [phCause]
  have hle : (phMeasure β x).real (Iio 1) ≤ (phMeasure β x).real (Iic 1) :=
    measureReal_mono Iio_subset_Iic_self
  have hI : (phMeasure β x).real (Iic 1) = 1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * 1)) := by
    rw [← cdf_eq_real, phMeasure, cdf_expMeasure_eq (Real.exp_pos _), ite_eq_left zero_le_one]
  rw [hs, probReal_compl_eq_one_sub measurableSet_Iio]
  have := Real.exp_pos (-(Real.exp (β ⬝ᵥ x) * 1))
  linarith

/-- The failure time is positive almost surely. -/
theorem ae_phTime_pos (β x : Fin p → ℝ) : ∀ᵐ ω ∂phMeasure β x, 0 < phTime ω := by
  have h0 : phMeasure β x (Iic 0) = 0 := by
    rw [← ofReal_cdf, phMeasure, cdf_expMeasure_eq (Real.exp_pos _), ite_eq_left le_rfl]
    simp
  refine ae_iff.2 (measure_mono_null (fun ω hω => ?_) h0)
  simp only [mem_ofPred_eq, not_lt] at hω
  simp only [mem_Iic]
  by_contra hpos
  rw [not_le] at hpos
  unfold phTime at hω
  split_ifs at hω with h
  · have : 0 < ω / (1 - ω) := div_pos hpos (by linarith)
    linarith
  · linarith

/-- The cumulative incidence of the cause of interest stays below `1`. -/
theorem cif_phMeasure_lt_one (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cif (phMeasure β x) phTime phCause true t < 1 := by
  rw [cif_phMeasure_of_nonneg β x ht]
  linarith [Real.exp_pos (-(Real.exp (β ⬝ᵥ x) * (t / (1 + t))))]

/-- The derivative of the cumulative incidence is interval integrable on `[0, t]`. -/
theorem intervalIntegrable_phCifDeriv (θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (phCifDeriv θ) volume 0 t := by
  refine ContinuousOn.intervalIntegrable fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  exact (continuousAt_phCifDeriv θ (by linarith [hs.1])).continuousWithinAt

/-- The cumulative incidence is continuous on `[0, t]`. -/
theorem continuousOn_cif_phMeasure (β x : Fin p → ℝ) (t : ℝ) :
    ContinuousOn (cif (phMeasure β x) phTime phCause true) (Icc 0 t) :=
  fun s hs => (continuousAt_cif_phMeasure β x (by linarith [hs.1])).continuousWithinAt

/-- **`IsPropSubdistHazards.cif_eq` for the family**:
`F_c(t; x) = 1 - exp (-exp ⟪β, x⟫ ∫₀ᵗ λ₀)` for `t ≥ 0`. -/
theorem cif_phMeasure_eq_integral (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cif (phMeasure β x) phTime phCause true t =
      1 - Real.exp (-(Real.exp (β ⬝ᵥ x) * ∫ s in (0 : ℝ)..t, phBaseline s)) :=
  (isPropSubdistHazards_phMeasure β).cif_eq measurable_phTime measurableSet_phCause x
    (ae_phTime_pos β x) ht (continuousOn_cif_phMeasure β x t)
    (fun _ hs => hasDerivAt_cif_phMeasure β x hs.1)
    (intervalIntegrable_phCifDeriv _ ht) (cif_phMeasure_lt_one β x ht)

/-- **`IsPropSubdistHazards.cif_eq_rpow` for the family**:
`F_c(t; x) = 1 - (1 - F_c(t; 0)) ^ exp ⟪β, x⟫` for `t ≥ 0`. -/
theorem cif_phMeasure_eq_rpow (β x : Fin p → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    cif (phMeasure β x) phTime phCause true t =
      1 - (1 - cif (phMeasure β 0) phTime phCause true t) ^ Real.exp (β ⬝ᵥ x) :=
  (isPropSubdistHazards_phMeasure β).cif_eq_rpow measurable_phTime measurableSet_phCause x
    (ae_phTime_pos β x) (ae_phTime_pos β 0) ht (continuousOn_cif_phMeasure β x t)
    (fun _ hs => hasDerivAt_cif_phMeasure β x hs.1)
    (intervalIntegrable_phCifDeriv _ ht) (cif_phMeasure_lt_one β x ht)
    (continuousOn_cif_phMeasure β 0 t) (fun _ hs => hasDerivAt_cif_phMeasure β 0 hs.1)
    (intervalIntegrable_phCifDeriv _ ht) (cif_phMeasure_lt_one β 0 ht)

end MathlibExt.Probability.Statistics.FineGrayPHFamily
