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

Discharges ECE roadmap leaf `ECE.COM.BPSK.L1` (BPSK sign error).
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

/-- Closed-form error of the threshold-`τ` detector with prior `p = P(S = +1)`. -/
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

private theorem pdfReal_continuous_aux :
    Continuous (gaussianPDFReal (0 : ℝ) 1) := by
  unfold gaussianPDFReal
  fun_prop

private theorem cdf_sub_eq_mass (u v : ℝ) (huv : u ≤ v) :
    cdf (gaussianReal 0 1) v - cdf (gaussianReal 0 1) u =
      (gaussianReal (0 : ℝ) 1).real (Set.Ioc u v) := by
  rw [cdf_eq_real, cdf_eq_real]
  have hunion : Set.Iic v = Set.Iic u ∪ Set.Ioc u v := by
    ext z
    simp only [Set.mem_Iic, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro h
      by_cases h1 : z ≤ u
      · exact Or.inl h1
      · exact Or.inr ⟨lt_of_not_ge h1, h⟩
    · rintro (h | ⟨_, h⟩)
      · exact h.trans huv
      · exact h
  have hdisj : Disjoint (Set.Iic u) (Set.Ioc u v) := by
    rw [Set.disjoint_left]
    intro z hx hxy'
    simp only [Set.mem_Iic, Set.mem_Ioc] at hx hxy'
    exact lt_irrefl u (hxy'.1.trans_le hx)
  rw [hunion, measureReal_union hdisj measurableSet_Ioc]
  ring

private theorem ioc_mass_bounds (u v lo hi : ℝ) (huv : u < v) (hlo : 0 ≤ lo)
    (h : ∀ x ∈ Set.Ioc u v,
      lo ≤ gaussianPDFReal (0 : ℝ) 1 x ∧ gaussianPDFReal (0 : ℝ) 1 x ≤ hi) :
    lo * (v - u) ≤ (gaussianReal (0 : ℝ) 1).real (Set.Ioc u v) ∧
      (gaussianReal (0 : ℝ) 1).real (Set.Ioc u v) ≤ hi * (v - u) := by
  have hmid_mem : (u + v) / 2 ∈ Set.Ioc u v := by
    simp only [Set.mem_Ioc]
    constructor <;> linarith
  obtain ⟨hlo_mid, hhi_mid⟩ := h ((u + v) / 2) hmid_mem
  have hhi0 : 0 ≤ hi := le_trans hlo (le_trans hlo_mid hhi_mid)
  have hENN_lo : ENNReal.ofReal (lo * (v - u)) ≤ (gaussianReal (0 : ℝ) 1) (Set.Ioc u v) := by
    rw [gaussianReal_apply _ (by simp : (1 : ℝ≥0) ≠ 0)]
    have h1 : (∫⁻ _ in Set.Ioc u v, ENNReal.ofReal lo) ≤
        ∫⁻ x in Set.Ioc u v, gaussianPDF (0 : ℝ) 1 x := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      apply Filter.Eventually.of_forall
      intro x hx
      obtain ⟨hlo_x, -⟩ := h x hx
      have hpdf : gaussianPDF (0 : ℝ) 1 x =
          ENNReal.ofReal (gaussianPDFReal (0 : ℝ) 1 x) := rfl
      rw [hpdf]
      exact ENNReal.ofReal_le_ofReal hlo_x
    rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hlo] at h1
    exact h1
  have hENN_hi : (gaussianReal (0 : ℝ) 1) (Set.Ioc u v) ≤ ENNReal.ofReal (hi * (v - u)) := by
    rw [gaussianReal_apply _ (by simp : (1 : ℝ≥0) ≠ 0)]
    have h2 : (∫⁻ x in Set.Ioc u v, gaussianPDF (0 : ℝ) 1 x) ≤
        ∫⁻ _ in Set.Ioc u v, ENNReal.ofReal hi := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      apply Filter.Eventually.of_forall
      intro x hx
      obtain ⟨-, hhi_x⟩ := h x hx
      have hpdf : gaussianPDF (0 : ℝ) 1 x =
          ENNReal.ofReal (gaussianPDFReal (0 : ℝ) 1 x) := rfl
      rw [hpdf]
      exact ENNReal.ofReal_le_ofReal hhi_x
    rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul hhi0] at h2
    exact h2
  have hlo_nn : 0 ≤ lo * (v - u) := mul_nonneg hlo (by linarith)
  have hhi_nn : 0 ≤ hi * (v - u) := mul_nonneg hhi0 (by linarith)
  have hfin : (gaussianReal (0 : ℝ) 1) (Set.Ioc u v) ≠ _ :=
    measure_ne_top _ _
  have hreal_eq : (gaussianReal (0 : ℝ) 1).real (Set.Ioc u v) =
      ENNReal.toReal ((gaussianReal (0 : ℝ) 1) (Set.Ioc u v)) := rfl
  constructor
  · have hlow : ENNReal.toReal (ENNReal.ofReal (lo * (v - u))) ≤
        ENNReal.toReal ((gaussianReal (0 : ℝ) 1) (Set.Ioc u v)) :=
      ENNReal.toReal_mono hfin hENN_lo
    rw [ENNReal.toReal_ofReal hlo_nn, ← hreal_eq] at hlow
    exact hlow
  · have hhigh : ENNReal.toReal ((gaussianReal (0 : ℝ) 1) (Set.Ioc u v)) ≤
        ENNReal.toReal (ENNReal.ofReal (hi * (v - u))) :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hENN_hi
    rw [ENNReal.toReal_ofReal hhi_nn, ← hreal_eq] at hhigh
    exact hhigh

private theorem exists_pos_case (p a σ : ℝ) (hp1 : 1 / 2 < p) (hp2 : p < 1)
    (ha : 0 < a) (hσ : 0 < σ) :
    ∃ τ : ℝ, thresholdErrorFormula p a σ τ < thresholdErrorFormula p a σ 0 := by
  have hσ' : σ ≠ 0 := ne_of_gt hσ
  have h1p : 0 < 1 - p := by linarith
  -- center c, peak M, ratio r, tolerance ε
  set c : ℝ := -a / σ with hc
  set M : ℝ := gaussianPDFReal (0 : ℝ) 1 c with hM
  have hMpos : 0 < M := gaussianPDFReal_pos 0 1 c (by simp)
  set r : ℝ := p / (1 - p) with hr
  have hr1 : 1 < r := by
    rw [hr, one_lt_div h1p]
    linarith
  have hrpos : 0 < r := by linarith
  set ε : ℝ := M * (r - 1) / (2 * (r + 1)) with hε
  have hr1ne : r + 1 ≠ 0 := ne_of_gt (by linarith)
  have hεpos : 0 < ε := by
    rw [hε]
    apply div_pos _ _ <;> nlinarith [hMpos, hr1, hrpos]
  have hεM : ε < M := by
    have hfrac : (r - 1) / (2 * (r + 1)) < 1 := by
      rw [div_lt_one (by positivity : 0 < 2 * (r + 1))]
      nlinarith [hr1]
    have hεeq : ε = M * ((r - 1) / (2 * (r + 1))) := by rw [hε]; ring
    rw [hεeq]
    calc M * ((r - 1) / (2 * (r + 1))) < M * 1 :=
            mul_lt_mul_of_pos_left hfrac hMpos
      _ = M := mul_one M
  have hMratio : (M + ε) / (M - ε) < r := by
    have hMε : 0 < M - ε := by linarith
    rw [div_lt_iff₀ hMε]
    -- M + ε < r * (M - ε)
    have hεeq : ε * (1 + r) = M * (r - 1) / 2 := by
      rw [hε]
      field_simp
      ring
    nlinarith [hεeq, hMpos, hr1, hrpos, hεpos, hεM]
  -- continuity gives δ₀
  have hcont : ContinuousAt (gaussianPDFReal (0 : ℝ) 1) c :=
    pdfReal_continuous_aux.continuousAt
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := (Metric.continuousAt_iff.mp hcont) ε hεpos
  -- δ := δ₀ * σ / 2
  set δ : ℝ := δ₀ * σ / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  have hδσ : δ / σ = δ₀ / 2 := by
    rw [hδ]
    field_simp
  have hδσpos : 0 < δ / σ := by positivity
  have hδσlt : δ / σ < δ₀ := by
    rw [hδσ]
    linarith
  -- intervals
  set u1 : ℝ := c - δ / σ with hu1
  set v2 : ℝ := c + δ / σ with hv2
  have hu1lt : u1 < c := by
    rw [hu1]
    linarith [hδσpos]
  have hclt : c < v2 := by
    rw [hv2]
    linarith [hδσpos]
  have hlen1 : c - u1 = δ / σ := by
    rw [hu1]
    ring
  have hlen2 : v2 - c = δ / σ := by
    rw [hv2]
    ring
  -- pdf bounds on both intervals
  have hbound1 : ∀ x ∈ Set.Ioc u1 c,
      M - ε ≤ gaussianPDFReal (0 : ℝ) 1 x ∧ gaussianPDFReal (0 : ℝ) 1 x ≤ M + ε := by
    intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hdist : dist x c < δ₀ := by
      rw [Real.dist_eq]
      have habs : |x - c| = c - x := by
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [habs]
      have : c - x < c - u1 := by linarith
      rw [hlen1] at this
      linarith [hδσlt, this]
    have hpd := hδ₀ hdist
    rw [Real.dist_eq] at hpd
    have habs2 : -ε < gaussianPDFReal (0 : ℝ) 1 x - M ∧
        gaussianPDFReal (0 : ℝ) 1 x - M < ε := abs_lt.mp hpd
    constructor <;> linarith
  have hbound2 : ∀ x ∈ Set.Ioc c v2,
      M - ε ≤ gaussianPDFReal (0 : ℝ) 1 x ∧ gaussianPDFReal (0 : ℝ) 1 x ≤ M + ε := by
    intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hdist : dist x c < δ₀ := by
      rw [Real.dist_eq]
      have habs : |x - c| = x - c := abs_of_nonneg (by linarith)
      rw [habs]
      have : x - c ≤ v2 - c := by linarith
      rw [hlen2] at this
      linarith [hδσlt, this]
    have hpd := hδ₀ hdist
    rw [Real.dist_eq] at hpd
    have habs2 : -ε < gaussianPDFReal (0 : ℝ) 1 x - M ∧
        gaussianPDFReal (0 : ℝ) 1 x - M < ε := abs_lt.mp hpd
    constructor <;> linarith
  have hlo0 : 0 ≤ M - ε := le_of_lt (by linarith)
  obtain ⟨hAlo, hAhi⟩ := ioc_mass_bounds u1 c (M - ε) (M + ε) hu1lt hlo0 hbound1
  obtain ⟨hBlo, hBhi⟩ := ioc_mass_bounds c v2 (M - ε) (M + ε) hclt hlo0 hbound2
  rw [hlen1] at hAlo hAhi
  rw [hlen2] at hBlo hBhi
  -- A B notation
  set A : ℝ := (gaussianReal (0 : ℝ) 1).real (Set.Ioc u1 c) with hA
  set B : ℝ := (gaussianReal (0 : ℝ) 1).real (Set.Ioc c v2) with hB
  have hApos : 0 < A := by
    have : 0 < (M - ε) * (δ / σ) := by
      apply mul_pos _ hδσpos
      linarith
    linarith [hAlo, this]
  have hLpos : 0 < δ / σ := hδσpos
  have hLne : δ / σ ≠ 0 := ne_of_gt hLpos
  have hlo_pos : 0 < M - ε := by linarith
  have hhi_pos : 0 < M + ε := by linarith [hMpos, hεpos]
  -- B / A < r
  have hBA : B / A < r := by
    have hMε_ne : M - ε ≠ 0 := ne_of_gt hlo_pos
    have hprod_ne : (M - ε) * (δ / σ) ≠ 0 := mul_ne_zero hMε_ne hLne
    have h1 : B / A ≤ ((M + ε) * (δ / σ)) / ((M - ε) * (δ / σ)) := by
      have hBnn : 0 ≤ B := le_trans (by positivity : 0 ≤ (M - ε) * (δ / σ)) hBlo
      have hAinv_nn : 0 ≤ 1 / A := by positivity
      have hAle : (M - ε) * (δ / σ) ≤ A := hAlo
      have hBle : B ≤ (M + ε) * (δ / σ) := hBhi
      have hAinv_le : 1 / A ≤ 1 / ((M - ε) * (δ / σ)) := by
        apply one_div_le_one_div_of_le _ hAle
        positivity
      calc B / A = B * (1 / A) := by ring
        _ ≤ ((M + ε) * (δ / σ)) * (1 / A) :=
          mul_le_mul_of_nonneg_right hBle hAinv_nn
        _ ≤ ((M + ε) * (δ / σ)) * (1 / ((M - ε) * (δ / σ))) :=
          mul_le_mul_of_nonneg_left hAinv_le (by positivity)
        _ = ((M + ε) * (δ / σ)) / ((M - ε) * (δ / σ)) := by ring
    have h2 : ((M + ε) * (δ / σ)) / ((M - ε) * (δ / σ)) = (M + ε) / (M - ε) := by
      field_simp
    rw [h2] at h1
    linarith [h1, hMratio]
  -- (1-p) * B < p * A
  have hmain : (1 - p) * B < p * A := by
    have hr_eq : r = p / (1 - p) := rfl
    rw [hr_eq] at hBA
    rw [div_lt_div_iff₀ hApos h1p] at hBA
    -- hBA : B * (1 - p) < p * A
    linarith [hBA]
  -- connect to formula with τ = -δ
  have hu1_eq : u1 = (-δ - a) / σ := by
    simp only [hu1, hc]
    field_simp
    ring
  have hv2_eq : v2 = (δ - a) / σ := by
    simp only [hv2, hc]
    field_simp
    ring
  have hc_eq : c = -a / σ := rfl
  have hAu : u1 ≤ c := le_of_lt hu1lt
  have hvc : c ≤ v2 := le_of_lt hclt
  have hA_eq : cdf (gaussianReal 0 1) c - cdf (gaussianReal 0 1) u1 = A :=
    cdf_sub_eq_mass u1 c hAu
  have hB_eq : cdf (gaussianReal 0 1) v2 - cdf (gaussianReal 0 1) c = B :=
    cdf_sub_eq_mass c v2 hvc
  have hf0 : thresholdErrorFormula p a σ 0 = cdf (gaussianReal 0 1) c := by
    rw [formula_zero_eq, hc_eq]
  have hfneg : thresholdErrorFormula p a σ (-δ) =
      p * cdf (gaussianReal 0 1) u1 + (1 - p) * cdf (gaussianReal 0 1) v2 := by
    unfold thresholdErrorFormula
    have e1 : ((-δ - a) / σ) = u1 := hu1_eq.symm
    have e2 : ((-δ + a) / σ) = -v2 := by
      simp only [hv2, hc]
      field_simp
      ring
    rw [e1, e2, symm_aux]
    ring
  use -δ
  rw [hfneg, hf0]
  -- goal: p*Φ(u1) + (1-p)*Φ(v2) < Φ(c)
  -- with Φ(u1) = Φ(c) - A, Φ(v2) = Φ(c) + B
  have hΦu : cdf (gaussianReal 0 1) u1 = cdf (gaussianReal 0 1) c - A := by linarith [hA_eq]
  have hΦv : cdf (gaussianReal 0 1) v2 = cdf (gaussianReal 0 1) c + B := by linarith [hB_eq]
  rw [hΦu, hΦv]
  nlinarith [hmain]

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
lemma prob_signError_eq_cdf_neg_div (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
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
lemma prob_signError_eq_gaussianQ_sqrt_two_bitEnergy_div (Ω : Type*)
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
      have hp1lt : p < 1 := lt_of_le_of_ne hp1 hp1'
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
        have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · -- p < 1/2: reduce to 1-p > 1/2 via threshold negation
          have hp1_gt : 1 / 2 < 1 - p := by linarith
          have hp1_lt : 1 - p < 1 := by linarith
          obtain ⟨τ', hτ'⟩ := exists_pos_case (1 - p) a σ hp1_gt hp1_lt hapos hσ
          use -τ'
          have h0eq : thresholdErrorFormula p a σ 0 =
              thresholdErrorFormula (1 - p) a σ 0 := by
            rw [formula_zero_eq, formula_zero_eq]
          rw [formula_neg_swap, h0eq]
          exact hτ'
        · -- p > 1/2: continuity argument
          exact exists_pos_case p a σ hgt hp1lt hapos hσ

end PhyslibExt.Communications.BPSKSignError
