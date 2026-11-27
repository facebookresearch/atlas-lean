/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import MathlibExt.Probability.Distributions.GaussianCdf

/-!
# BPSK sign-detector error probability

## i. Overview

Binary phase-shift keying with a sign detector: for equiprobable
symbols `±a` and an independent Gaussian matched-filter component
of variance `σ²`, the label-error probability is `Φ(-a/σ)`, i.e.
`Q(a/σ)` for the Gaussian Q function, and with the unit-energy
conventions `Eb = a²`, `σ² = N0/2` it is `Q(√(2Eb/N0))`. At zero
amplitude the error is `1/2`. For priors other than `1/2`, the
zero threshold is not optimal.

## ii. Key results

- `prob_signError_eq_cdf_neg_div` and
  `prob_signError_eq_gaussianQ_sqrt_two_bitEnergy_div`: the error
  probability in CDF, Q and energy forms.
- `prob_signError_eq_half_of_amplitude_zero`: the `a = 0` case.
- `exists_threshold_lt_zero_threshold_of_prior_ne_half`: unequal
  priors admit a strictly better threshold.

## iii. Table of contents

- A. The sign-detector error probability

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog Communication
Systems*, fifth edition, Oxford University Press, 2019: binary signaling over the Gaussian channel and the
  Q-function error form.

## A. The sign-detector error probability
-/

@[expose] public section

namespace PhyslibExt.Communications.BPSKSignError

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

/-- The real matched-filter sample for label `s ∈ {-1, +1}`, amplitude `a`, noise `n`. -/
def receivedSample (a : ℝ) (s : ℤ) (n : ℝ) : ℝ :=
  a * (s : ℝ) + n

/-- Threshold detector: returns label `+1` when `τ ≤ y`, else `-1`. -/
noncomputable def thresholdDetector (τ y : ℝ) : ℤ :=
  if τ ≤ y then 1 else -1

/-- The sign detector: the threshold detector at threshold `0`. -/
noncomputable def signDetector (y : ℝ) : ℤ :=
  thresholdDetector 0 y

/-- The event that the threshold-`τ` detector returns a label different from `S`. -/
def thresholdErrorEvent (Ω : Type*) (a τ : ℝ) (S : Ω → ℤ) (Nz : Ω → ℝ) : Set Ω :=
  {ω | thresholdDetector τ (receivedSample a (S ω) (Nz ω)) ≠ S ω}

/-- The event that the sign detector returns a label different from `S`. -/
def signErrorEvent (Ω : Type*) (a : ℝ) (S : Ω → ℤ) (Nz : Ω → ℝ) : Set Ω :=
  {ω | signDetector (receivedSample a (S ω) (Nz ω)) ≠ S ω}

/-- The Gaussian tail `Q(x) = 1 - Φ(x)` with `Φ = cdf (gaussianReal 0 1)`. -/
noncomputable def gaussianQ (x : ℝ) : ℝ :=
  1 - cdf (gaussianReal 0 1) x

/-- Declared bit-energy convention `Eb = a^2` for a unit-energy basis. -/
def bitEnergy (a : ℝ) : ℝ :=
  a ^ 2

/-- Closed-form error of the threshold-`τ` detector with prior `p = P(S = +1)`:
`p Φ((τ - a)/σ) + (1 - p)(1 - Φ((τ + a)/σ))`. It is that error probability for a prior
`0 ≤ p ≤ 1` and a noise standard deviation `σ > 0`, the hypotheses of `prob_thresholdError_eq`;
the formula is defined for all reals, and outside that range it is not a probability (for
`σ = 0` it is `1/2` for every `p`, `a` and `τ`, because `x / 0 = 0`, and for `p > 1` it can
exceed `1`). -/
noncomputable def thresholdErrorFormula (p a σ τ : ℝ) : ℝ :=
  p * cdf (gaussianReal 0 1) ((τ - a) / σ) +
    (1 - p) * (1 - cdf (gaussianReal 0 1) ((τ + a) / σ))

private theorem detector_eq_one_iff (τ y : ℝ) :
    thresholdDetector τ y = 1 ↔ τ ≤ y := by
  unfold thresholdDetector
  by_cases h : τ ≤ y <;> simp [h]

private theorem symm_aux (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = 1 - cdf (gaussianReal 0 1) x := by
  exact ProbabilityTheory.cdf_gaussianReal_neg x

private theorem std_aux (σ x : ℝ) (hσ : 0 < σ) :
    cdf (gaussianReal 0 (σ ^ 2).toNNReal) x = cdf (gaussianReal 0 1) (x / σ) := by
  have hv : (σ ^ 2).toNNReal ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero, not_le]
    exact pow_pos hσ 2
  rw [ProbabilityTheory.cdf_gaussianReal_eq_std 0 x hv, sub_zero,
    Real.coe_toNNReal _ (sq_nonneg σ), Real.sqrt_sq (le_of_lt hσ)]

private theorem var_ne_zero_aux (σ : ℝ) (hσ : 0 < σ) :
    (σ ^ 2).toNNReal ≠ 0 := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have h_eq : (σ ^ 2).toNNReal = NNReal.mk (σ ^ 2) (sq_nonneg σ) := by
    ext
    simp [Real.coe_toNNReal', NNReal.coe_mk, max_eq_left (sq_nonneg σ)]
  rw [h_eq]
  intro h
  have hcoe : ((NNReal.mk (σ ^ 2) (sq_nonneg σ) : ℝ≥0) : ℝ) = 0 := by
    rw [h]; simp
  rw [NNReal.coe_mk] at hcoe
  exact pow_ne_zero 2 hσ' hcoe

private theorem iio_eq_iic_real (c : ℝ) (σ : ℝ) (hσ : 0 < σ) :
    (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Iio c) =
      (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Iic c) := by
  have hnull : NullSingletonClass (gaussianReal 0 (σ ^ 2).toNNReal) :=
    nullSingletonClass_gaussianReal (var_ne_zero_aux σ hσ)
  have hsing : (gaussianReal 0 (σ ^ 2).toNNReal).real {c} = 0 := by
    have h0 : (gaussianReal 0 (σ ^ 2).toNNReal) {c} = 0 :=
      @measure_singleton _ _ _ hnull c
    simp [Measure.real, h0]
  have hunion : Set.Iic c = Set.Iio c ∪ {c} := by
    ext y
    simp only [Set.mem_Iic, Set.mem_Iio, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq
    · rintro (hlt | rfl)
      · exact le_of_lt hlt
      · exact le_rfl
  have hdisj : Disjoint (Set.Iio c) ({c} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro y hy hx
    simp only [Set.mem_Iio, Set.mem_singleton_iff] at hy hx
    rw [hx] at hy
    exact lt_irrefl c hy
  rw [hunion, measureReal_union hdisj (MeasurableSet.singleton c), hsing, add_zero]

private theorem ici_eq_one_sub_cdf (c σ : ℝ) (hσ : 0 < σ) :
    (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Ici c) =
      1 - cdf (gaussianReal 0 (σ ^ 2).toNNReal) c := by
  have hnull : NullSingletonClass (gaussianReal 0 (σ ^ 2).toNNReal) :=
    nullSingletonClass_gaussianReal (var_ne_zero_aux σ hσ)
  rw [cdf_eq_real]
  have hIci_union : Set.Ici c = Set.Ioi c ∪ {c} := by
    ext y
    simp only [Set.mem_Ici, Set.mem_Ioi, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr heq.symm
    · rintro (hlt | rfl)
      · exact le_of_lt hlt
      · exact le_rfl
  have hdisj : Disjoint (Set.Ioi c) ({c} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro y hy hx
    simp only [Set.mem_Ioi, Set.mem_singleton_iff] at hy hx
    rw [hx] at hy
    exact lt_irrefl c hy
  have hsing : (gaussianReal 0 (σ ^ 2).toNNReal).real {c} = 0 := by
    have h0 : (gaussianReal 0 (σ ^ 2).toNNReal) {c} = 0 :=
      @measure_singleton _ _ _ hnull c
    simp [Measure.real, h0]
  have hIci_real : (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Ici c) =
      (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Ioi c) := by
    rw [hIci_union, measureReal_union hdisj (MeasurableSet.singleton c), hsing, add_zero]
  rw [hIci_real]
  have hcompl : Set.Ioi c = (Set.Iic c)ᶜ := Set.compl_Iic.symm
  rw [hcompl, measureReal_compl measurableSet_Iic, probReal_univ]

private theorem event_pos_eq (Ω : Type*) (a τ : ℝ) (S : Ω → ℤ) (Nz : Ω → ℝ) :
    thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = 1}
      = S ⁻¹' ({1} : Set ℤ) ∩ Nz ⁻¹' (Set.Iio (τ - a)) := by
  ext ω
  simp only [thresholdErrorEvent, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_Iio, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨herr, hS⟩
    rw [hS] at herr
    simp only [receivedSample, Int.cast_one, mul_one] at herr
    have hle : ¬ τ ≤ a + Nz ω := by
      intro hle
      have h1 : thresholdDetector τ (a + Nz ω) = 1 :=
        (detector_eq_one_iff _ _).mpr hle
      exact herr h1
    have hlt : Nz ω < τ - a := by linarith [not_le.mp hle]
    exact ⟨hS, hlt⟩
  · rintro ⟨hS, hNz⟩
    refine ⟨?_, hS⟩
    rw [hS]
    simp only [receivedSample, Int.cast_one, mul_one]
    intro hcon
    have hle : τ ≤ a + Nz ω := (detector_eq_one_iff _ _).mp hcon
    linarith

private theorem event_neg_eq (Ω : Type*) (a τ : ℝ) (S : Ω → ℤ) (Nz : Ω → ℝ) :
    thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = -1}
      = S ⁻¹' ({-1} : Set ℤ) ∩ Nz ⁻¹' (Set.Ici (τ + a)) := by
  ext ω
  simp only [thresholdErrorEvent, Set.mem_inter_iff, Set.mem_preimage,
    Set.mem_singleton_iff, Set.mem_Ici, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨herr, hS⟩
    rw [hS] at herr
    simp only [receivedSample, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at herr
    have hle : τ ≤ -a + Nz ω := by
      by_contra hcon
      have hlt : -a + Nz ω < τ := lt_of_not_ge hcon
      have hnl : ¬ τ ≤ -a + Nz ω := not_le_of_gt hlt
      have hneg : thresholdDetector τ (-a + Nz ω) = -1 := by
        unfold thresholdDetector
        simp [hnl]
      exact herr hneg
    have hge : τ + a ≤ Nz ω := by linarith
    exact ⟨hS, hge⟩
  · rintro ⟨hS, hNz⟩
    refine ⟨?_, hS⟩
    rw [hS]
    simp only [receivedSample, Int.cast_neg, Int.cast_one, mul_neg, mul_one]
    intro hcon
    have hle : τ ≤ -a + Nz ω := by linarith
    have h1 : thresholdDetector τ (-a + Nz ω) = 1 :=
      (detector_eq_one_iff _ _).mpr hle
    rw [h1] at hcon
    simp at hcon

private theorem cdf_std_zero : cdf (gaussianReal 0 1) 0 = 1 / 2 := by
  exact ProbabilityTheory.cdf_gaussianReal_zero

private theorem strictMono_cdf_std_aux : StrictMono (cdf (gaussianReal 0 1)) := by
  exact ProbabilityTheory.strictMono_cdf_gaussianReal 0 one_ne_zero

private theorem formula_zero_eq (p a σ : ℝ) :
    thresholdErrorFormula p a σ 0 = cdf (gaussianReal 0 1) (-a / σ) := by
  unfold thresholdErrorFormula
  have h1 : ((0 : ℝ) - a) / σ = -a / σ := by ring
  have h2 : ((0 : ℝ) + a) / σ = a / σ := by ring
  rw [h1, h2]
  have hsym : cdf (gaussianReal 0 1) (-(a / σ)) = 1 - cdf (gaussianReal 0 1) (a / σ) :=
    symm_aux (a / σ)
  have hneg : -a / σ = -(a / σ) := by ring
  rw [hneg, hsym]
  ring

private theorem formula_neg_swap (p a σ τ : ℝ) :
    thresholdErrorFormula p a σ (-τ) = thresholdErrorFormula (1 - p) a σ τ := by
  unfold thresholdErrorFormula
  have e1 : ((-τ - a) / σ) = -((τ + a) / σ) := by ring
  have e2 : ((-τ + a) / σ) = -((τ - a) / σ) := by ring
  rw [e1, e2, symm_aux, symm_aux]
  ring

private theorem gaussianPDFReal_std_neg (x : ℝ) :
    gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDFReal_def]

/-- The threshold error has derivative `(2p - 1) φ(a / σ) / σ` at threshold `0`. -/
private theorem hasDerivAt_thresholdErrorFormula_zero (p a σ : ℝ) :
    HasDerivAt (thresholdErrorFormula p a σ)
      ((2 * p - 1) * gaussianPDFReal 0 1 (a / σ) / σ) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => (τ - a) / σ) (1 / σ) 0 :=
    ((hasDerivAt_id' 0).sub_const a).div_const σ
  have hr : HasDerivAt (fun τ : ℝ => (τ + a) / σ) (1 / σ) 0 :=
    ((hasDerivAt_id' 0).add_const a).div_const σ
  have h := (((hasDerivAt_stdNormal_cdf ((0 - a) / σ)).comp 0 hl).const_mul p).add
    ((((hasDerivAt_stdNormal_cdf ((0 + a) / σ)).comp 0 hr).const_sub 1).const_mul (1 - p))
  have e1 : (0 - a) / σ = -(a / σ) := by ring
  have e2 : (0 + a) / σ = a / σ := by ring
  rw [e1, e2, gaussianPDFReal_std_neg] at h
  convert h using 1
  · rfl
  · ring

/-- For `p > 1/2` the derivative at `0` is positive, so a slightly negative threshold
is strictly better than `0`. -/
private theorem exists_pos_case (p a σ : ℝ) (hp1 : 1 / 2 < p) (hσ : 0 < σ) :
    ∃ τ : ℝ, thresholdErrorFormula p a σ τ < thresholdErrorFormula p a σ 0 := by
  have hD : 0 < (2 * p - 1) * gaussianPDFReal 0 1 (a / σ) / σ := by
    have hφ := gaussianPDFReal_pos 0 1 (a / σ) one_ne_zero
    have h2p : 0 < 2 * p - 1 := by linarith
    positivity
  have hev := (hasDerivAt_thresholdErrorFormula_zero p a σ).tendsto_slope_zero_left.eventually
    (lt_mem_nhds hD)
  obtain ⟨t, ht, htneg⟩ := (hev.and self_mem_nhdsWithin).exists
  rw [zero_add, smul_eq_mul] at ht
  exact ⟨t, by linarith [neg_of_mul_pos_right ht (inv_nonpos.mpr (le_of_lt htneg))]⟩

/-- `Φ(-x) = Q(x)`: the symmetry of the standard normal cdf in `Q` form. -/
lemma cdf_neg_eq_gaussianQ (x : ℝ) :
    cdf (gaussianReal 0 1) (-x) = gaussianQ x := by
  unfold gaussianQ
  exact symm_aux x

/-- The sign detector is the threshold detector at `0`, so the error events agree. -/
lemma signErrorEvent_eq_thresholdErrorEvent_zero (Ω : Type*) (a : ℝ) (S : Ω → ℤ)
    (Nz : Ω → ℝ) :
    signErrorEvent Ω a S Nz = thresholdErrorEvent Ω a 0 S Nz := by
  rfl

/-- Error jointly with label `+1`: `P(error ∧ S = 1) = p * Φ((τ - a) / σ)`. -/
lemma prob_thresholdError_inter_label_pos (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → ℤ) (Nz : Ω → ℝ) (a σ τ p : ℝ)
    (hσ : 0 < σ) (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = p)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = 1}) =
      p * cdf (gaussianReal 0 1) ((τ - a) / σ) := by
  rw [event_pos_eq]
  have hs : MeasurableSet ({1} : Set ℤ) := MeasurableSet.singleton 1
  have ht : MeasurableSet (Set.Iio (τ - a)) := measurableSet_Iio
  have hmul := hindep.measure_inter_preimage_eq_mul _ _ hs ht
  have hreal : P.real (S ⁻¹' ({1} : Set ℤ) ∩ Nz ⁻¹' (Set.Iio (τ - a)))
      = P.real (S ⁻¹' ({1} : Set ℤ)) * P.real (Nz ⁻¹' (Set.Iio (τ - a))) := by
    rw [Measure.real, hmul, ENNReal.toReal_mul, ← Measure.real, ← Measure.real]
  rw [hreal]
  have hS_eq : S ⁻¹' ({1} : Set ℤ) = {ω | S ω = 1} := rfl
  rw [hS_eq, hprior]
  have hNz : P.real (Nz ⁻¹' (Set.Iio (τ - a)))
      = cdf (gaussianReal 0 1) ((τ - a) / σ) := by
    have hmap_eq : P.real (Nz ⁻¹' (Set.Iio (τ - a)))
        = (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Iio (τ - a)) := by
      rw [← hN.map_eq,
        map_measureReal_apply_of_aemeasurable hN.aemeasurable measurableSet_Iio]
    rw [hmap_eq, iio_eq_iic_real _ _ hσ, ← cdf_eq_real, std_aux _ _ hσ]
  rw [hNz]

/-- Error jointly with label `-1`: `P(error ∧ S = -1) = (1 - p) * (1 - Φ((τ + a) / σ))`. -/
lemma prob_thresholdError_inter_label_neg (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → ℤ) (Nz : Ω → ℝ) (a σ τ p : ℝ)
    (hσ : 0 < σ) (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = p)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = -1}) =
      (1 - p) * (1 - cdf (gaussianReal 0 1) ((τ + a) / σ)) := by
  rw [event_neg_eq]
  have hs : MeasurableSet ({-1} : Set ℤ) := MeasurableSet.singleton (-1)
  have ht : MeasurableSet (Set.Ici (τ + a)) := measurableSet_Ici
  have hmul := hindep.measure_inter_preimage_eq_mul _ _ hs ht
  have hreal : P.real (S ⁻¹' ({-1} : Set ℤ) ∩ Nz ⁻¹' (Set.Ici (τ + a)))
      = P.real (S ⁻¹' ({-1} : Set ℤ)) * P.real (Nz ⁻¹' (Set.Ici (τ + a))) := by
    rw [Measure.real, hmul, ENNReal.toReal_mul, ← Measure.real, ← Measure.real]
  rw [hreal]
  have hS_eq : S ⁻¹' ({-1} : Set ℤ) = {ω | S ω = -1} := rfl
  have hprior_neg : P.real (S ⁻¹' ({-1} : Set ℤ)) = 1 - p := by
    rw [hS_eq]
    have hunion : ({ω | S ω = 1} : Set Ω) ∪ {ω | S ω = -1} = Set.univ := by
      ext ω
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact hSval ω
    have hdisj : Disjoint ({ω | S ω = 1} : Set Ω) {ω | S ω = -1} := by
      rw [Set.disjoint_left]
      intro ω h1 h2
      simp only [Set.mem_ofPred_eq] at h1 h2
      rw [h1] at h2
      simp at h2
    have h2meas : MeasurableSet ({ω | S ω = -1} : Set Ω) :=
      hSmeas (MeasurableSet.singleton (-1))
    have hun : P.real (({ω | S ω = 1} : Set Ω) ∪ {ω | S ω = -1}) = 1 := by
      rw [hunion, probReal_univ]
    rw [measureReal_union hdisj h2meas] at hun
    rw [hprior] at hun
    linarith
  rw [hprior_neg]
  have hNz : P.real (Nz ⁻¹' (Set.Ici (τ + a)))
      = 1 - cdf (gaussianReal 0 1) ((τ + a) / σ) := by
    have hmap_eq : P.real (Nz ⁻¹' (Set.Ici (τ + a)))
        = (gaussianReal 0 (σ ^ 2).toNNReal).real (Set.Ici (τ + a)) := by
      rw [← hN.map_eq,
        map_measureReal_apply_of_aemeasurable hN.aemeasurable measurableSet_Ici]
    rw [hmap_eq, ici_eq_one_sub_cdf _ _ hσ, std_aux _ _ hσ]
  rw [hNz]

/-- Error of the threshold-`τ` detector for any prior `p` and any real amplitude `a`. -/
lemma prob_thresholdError_eq (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℤ) (Nz : Ω → ℝ) (a σ τ p : ℝ) (hσ : 0 < σ)
    (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = p)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (thresholdErrorEvent Ω a τ S Nz) = thresholdErrorFormula p a σ τ := by
  have hunion : thresholdErrorEvent Ω a τ S Nz
      = (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = 1}) ∪
        (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = -1}) := by
    ext ω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro herr
      rcases hSval ω with h | h
      · exact Or.inl ⟨herr, h⟩
      · exact Or.inr ⟨herr, h⟩
    · rintro (⟨herr, _⟩ | ⟨herr, _⟩)
      · exact herr
      · exact herr
  have hdisj : Disjoint (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = 1})
      (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = -1}) := by
    rw [Set.disjoint_left]
    rintro ω ⟨_, h1⟩ ⟨_, h2⟩
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [h1] at h2
    simp at h2
  have hnull2 : NullMeasurableSet
      (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = -1}) P := by
    rw [event_neg_eq]
    apply NullMeasurableSet.inter
    · exact (hSmeas (MeasurableSet.singleton (-1))).nullMeasurableSet
    · exact hN.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
  have haedisj : AEDisjoint P (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = 1})
      (thresholdErrorEvent Ω a τ S Nz ∩ {ω | S ω = -1}) :=
    hdisj.aedisjoint
  rw [hunion, measureReal_union₀ hnull2 haedisj]
  rw [prob_thresholdError_inter_label_pos Ω P S Nz a σ τ p hσ hSmeas hSval hprior hN
    hindep]
  rw [prob_thresholdError_inter_label_neg Ω P S Nz a σ τ p hσ hSmeas hSval hprior hN
    hindep]
  rfl

/-- At equal priors and threshold `0` the closed form is `Φ(-a / σ)`. -/
lemma thresholdErrorFormula_half_zero (a σ : ℝ) (hσ : 0 < σ) :
    thresholdErrorFormula (1 / 2) a σ 0 = cdf (gaussianReal 0 1) (-a / σ) := by
  unfold thresholdErrorFormula
  have h1 : ((0 : ℝ) - a) / σ = -a / σ := by ring
  have h2 : ((0 : ℝ) + a) / σ = a / σ := by ring
  rw [h1, h2]
  have hsym : cdf (gaussianReal 0 1) (-(a / σ)) = 1 - cdf (gaussianReal 0 1) (a / σ) :=
    symm_aux (a / σ)
  have hneg : -a / σ = -(a / σ) := by ring
  rw [hneg, hsym]
  ring

/-- **BPSK sign-detector error.** Equiprobable labels `±1`, amplitude `a ≥ 0`, noise
`N(0, σ^2)` independent of the label, `σ > 0`: the sign detector errs with probability
`Φ(-a / σ)`, where `Φ = cdf (gaussianReal 0 1)`. -/
theorem prob_signError_eq_cdf_neg_div (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℤ) (Nz : Ω → ℝ) (a σ : ℝ) (ha : 0 ≤ a)
    (hσ : 0 < σ) (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = 1 / 2)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (signErrorEvent Ω a S Nz) = cdf (gaussianReal 0 1) (-a / σ) := by
  rw [signErrorEvent_eq_thresholdErrorEvent_zero,
    prob_thresholdError_eq Ω P S Nz a σ 0 (1 / 2) hσ hSmeas hSval hprior hN hindep,
    thresholdErrorFormula_half_zero a σ hσ]

/-- The same error in `Q` form: `Φ(-a / σ) = Q(a / σ)`. -/
lemma prob_signError_eq_gaussianQ_div (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℤ) (Nz : Ω → ℝ) (a σ : ℝ) (ha : 0 ≤ a)
    (hσ : 0 < σ) (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = 1 / 2)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (signErrorEvent Ω a S Nz) = gaussianQ (a / σ) := by
  rw [prob_signError_eq_cdf_neg_div Ω P S Nz a σ ha hσ hSmeas hSval hprior hN hindep]
  have hneg : -a / σ = -(a / σ) := by ring
  rw [hneg, cdf_neg_eq_gaussianQ]

/-- Under the conventions `Eb = a^2`, `σ^2 = N0 / 2`, `N0 > 0`, `a ≥ 0`, `σ > 0`:
`a / σ = √(2 Eb / N0)`. -/
lemma div_eq_sqrt_two_bitEnergy_div (a σ N0 : ℝ) (ha : 0 ≤ a) (hσ : 0 < σ)
    (hN0 : 0 < N0) (hvar : σ ^ 2 = N0 / 2) :
    a / σ = Real.sqrt (2 * bitEnergy a / N0) := by
  unfold bitEnergy
  have h1 : 0 ≤ (2 * a ^ 2 / N0) := by positivity
  have h2 : 0 ≤ a / σ := by positivity
  rw [eq_comm, Real.sqrt_eq_iff_eq_sq h1 h2]
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have hN0' : N0 ≠ 0 := ne_of_gt hN0
  field_simp
  nlinarith [hvar, sq_nonneg a, sq_nonneg σ]

/-- **BPSK error in `Eb/N0` form.** Under the declared conventions `Eb = a^2` and
`σ^2 = N0 / 2` with `N0 > 0`, the sign-detector error is `Q(√(2 Eb / N0))`. -/
theorem prob_signError_eq_gaussianQ_sqrt_two_bitEnergy_div (Ω : Type*)
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → ℤ)
    (Nz : Ω → ℝ) (a σ N0 : ℝ) (ha : 0 ≤ a) (hσ : 0 < σ) (hN0 : 0 < N0)
    (hvar : σ ^ 2 = N0 / 2) (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = 1 / 2)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (signErrorEvent Ω a S Nz) = gaussianQ (Real.sqrt (2 * bitEnergy a / N0)) := by
  rw [prob_signError_eq_gaussianQ_div Ω P S Nz a σ ha hσ hSmeas hSval hprior hN hindep,
    div_eq_sqrt_two_bitEnergy_div a σ N0 ha hσ hN0 hvar]

/-- Boundary case `a = 0`: the amplitudes coincide but labels still differ, and the
sign detector errs with probability exactly `1 / 2`. -/
lemma prob_signError_eq_half_of_amplitude_zero (Ω : Type*) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → ℤ) (Nz : Ω → ℝ) (σ : ℝ)
    (hσ : 0 < σ) (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = 1 / 2)
    (hN : HasLaw Nz (gaussianReal 0 (σ ^ 2).toNNReal) P) (hindep : IndepFun S Nz P) :
    P.real (signErrorEvent Ω 0 S Nz) = 1 / 2 := by
  rw [prob_signError_eq_cdf_neg_div Ω P S Nz 0 σ le_rfl hσ hSmeas hSval hprior hN
    hindep]
  have h0 : (-0 : ℝ) / σ = 0 := by simp
  rw [h0, cdf_std_zero]

/-- A larger amplitude strictly lowers the error `Φ(-a / σ)` on `a ≥ 0`. -/
lemma cdf_neg_div_strictAntiOn (σ : ℝ) (hσ : 0 < σ) :
    StrictAntiOn (fun a : ℝ => cdf (gaussianReal 0 1) (-a / σ)) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hlt : -b / σ < -a / σ := by gcongr
  exact strictMono_cdf_std_aux hlt

/-- The error `Φ(-a / σ)` tends to `0` as `a → ∞`. -/
lemma tendsto_cdf_neg_div_atTop (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun a : ℝ => cdf (gaussianReal 0 1) (-a / σ)) atTop (𝓝 0) := by
  have hneg : -σ < 0 := neg_lt_zero.mpr hσ
  have h1 : Tendsto (fun a : ℝ => a / (-σ)) atTop atBot :=
    tendsto_id.atTop_div_const_of_neg hneg
  have heq2 : (fun a : ℝ => cdf (gaussianReal 0 1) (-a / σ))
      = (fun a : ℝ => cdf (gaussianReal 0 1) (a / (-σ))) := by
    ext a
    congr 1
    rw [div_neg, neg_div]
  rw [heq2]
  exact (tendsto_cdf_atBot _).comp h1

/-- Violated premise: with unequal priors `p ≠ 1/2`, some threshold strictly beats
threshold `0`, so the sign detector is not error-optimal there. -/
lemma exists_threshold_lt_zero_threshold_of_prior_ne_half (p a σ : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (hp : p ≠ 1 / 2) (ha : 0 ≤ a) (hσ : 0 < σ) :
    ∃ τ : ℝ, thresholdErrorFormula p a σ τ < thresholdErrorFormula p a σ 0 := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  by_cases hp0' : p = 0
  · -- p = 0: error is 1 - Φ((τ+a)/σ); τ = 1 beats 0
    subst hp0'
    use 1
    have hlt : a / σ < (1 + a) / σ := by
      rw [div_lt_div_iff_of_pos_right hσ]
      linarith
    have hPhi : cdf (gaussianReal 0 1) (a / σ) < cdf (gaussianReal 0 1) ((1 + a) / σ) :=
      strictMono_cdf_std_aux hlt
    have e0 : ((0 : ℝ) + a) / σ = a / σ := by ring
    unfold thresholdErrorFormula
    rw [e0]
    simp only [zero_mul, sub_zero, one_mul, zero_add]
    linarith
  · by_cases hp1' : p = 1
    · -- p = 1: error is Φ((τ-a)/σ); τ = -1 beats 0
      subst hp1'
      use -1
      have hlt : (-1 - a) / σ < -a / σ := by
        rw [div_lt_div_iff_of_pos_right hσ]
        linarith
      have hPhi : cdf (gaussianReal 0 1) ((-1 - a) / σ) < cdf (gaussianReal 0 1) (-a / σ) :=
        strictMono_cdf_std_aux hlt
      have e0 : ((0 : ℝ) - a) / σ = -a / σ := by ring
      unfold thresholdErrorFormula
      rw [e0]
      simp only [one_mul, sub_self, zero_mul, add_zero]
      linarith
    · -- 0 < p < 1
      have hp0pos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp0')
      by_cases ha0 : a = 0
      · -- a = 0: closed form is (1-p) + (2p-1)·Φ(τ/σ); τ = ±σ beats 0
        subst ha0
        have h0 : thresholdErrorFormula p 0 σ 0 = 1 / 2 := by
          unfold thresholdErrorFormula
          have e1 : ((0 : ℝ) - 0) / σ = 0 := by simp
          have e2 : ((0 : ℝ) + 0) / σ = 0 := by simp
          rw [e1, e2, cdf_std_zero]
          ring
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · use σ
          have e1 : ((σ - 0) / σ) = 1 := by simp [sub_zero, div_self hσ']
          have e2 : ((σ + 0) / σ) = 1 := by simp [add_zero, div_self hσ']
          rw [h0]
          unfold thresholdErrorFormula
          rw [e1, e2]
          have hPhi : (1 : ℝ) / 2 < cdf (gaussianReal 0 1) 1 := by
            rw [← cdf_std_zero]
            apply strictMono_cdf_std_aux
            norm_num
          have h2p : 2 * p - 1 < 0 := by linarith
          have hform : p * cdf (gaussianReal 0 1) 1 + (1 - p) * (1 - cdf (gaussianReal 0 1) 1)
              = (1 - p) + (2 * p - 1) * cdf (gaussianReal 0 1) 1 := by ring
          rw [hform]
          have hmul : (2 * p - 1) * cdf (gaussianReal 0 1) 1 < (2 * p - 1) * (1 / 2) :=
            mul_lt_mul_of_neg_left hPhi h2p
          linarith
        · use -σ
          have e1 : ((-σ - 0) / σ) = -1 := by simp [sub_zero, neg_div, div_self hσ']
          have e2 : ((-σ + 0) / σ) = -1 := by simp [add_zero, neg_div, div_self hσ']
          rw [h0]
          unfold thresholdErrorFormula
          rw [e1, e2]
          have hPhi : cdf (gaussianReal 0 1) (-1) < (1 : ℝ) / 2 := by
            rw [← cdf_std_zero]
            apply strictMono_cdf_std_aux
            norm_num
          have h2p : 0 < 2 * p - 1 := by linarith
          have hform : p * cdf (gaussianReal 0 1) (-1) + (1 - p) * (1 - cdf (gaussianReal 0 1) (-1))
              = (1 - p) + (2 * p - 1) * cdf (gaussianReal 0 1) (-1) := by ring
          rw [hform]
          have hmul : (2 * p - 1) * cdf (gaussianReal 0 1) (-1) < (2 * p - 1) * (1 / 2) :=
            mul_lt_mul_of_pos_left hPhi h2p
          linarith
      · -- a > 0
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · -- p < 1/2: reduce to 1-p > 1/2 via threshold negation
          have hp1_gt : 1 / 2 < 1 - p := by linarith
          obtain ⟨τ', hτ'⟩ := exists_pos_case (1 - p) a σ hp1_gt hσ
          use -τ'
          have h0eq : thresholdErrorFormula p a σ 0 =
              thresholdErrorFormula (1 - p) a σ 0 := by
            rw [formula_zero_eq, formula_zero_eq]
          rw [formula_neg_swap, h0eq]
          exact hτ'
        · -- p > 1/2: derivative-sign argument
          exact exists_pos_case p a σ hgt hσ

end PhyslibExt.Communications.BPSKSignError
