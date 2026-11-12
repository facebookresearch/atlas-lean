/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandPower

/-!
# Tests for the explicit PRDS p-value family for zero-ATE endpoints

* The uniform law on `[0, 1]` (`unif`) and one cluster `U = id` (comonotone p-values), and the
  product of two uniforms with two clusters (independent p-values).
* Boundary computations from the definitions, not through the theorems under test: the
  non-null Lehmann p-value `max ω 0 ^ 2` has `P(p ≤ 1/4) = 1/2`, matching
  `measure_lehmannPValue_le` (`(1/4) ^ (1/2) = 1/2`); it is not a valid p-value; and the two
  p-values of one cluster are not independent, so `isPRDSOn_lehmannPValue` goes beyond
  `isPRDSOn_of_iIndepFun`.
* A randomized trial on `[0, 1]` (treated: `ω ≤ 1/2`, constant potential outcomes, endpoint `0`
  with ATE `0`, endpoint `1` with ATE `2`, `ateNulls = {0}`): every hypothesis of the BH-FDR,
  Holm-FWER, power and consistency theorems is discharged.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Causality
  MathlibExt.Probability.Statistics.MultipleTesting Filter Topology

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandPower

/-! ### The uniform law and the comonotone (one-cluster) family -/

/-- The uniform law on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif :=
  ⟨by simp [Real.volume_Icc]⟩

lemma unif_Iic {s : ℝ} (h₁ : s ≤ 1) : unif (Set.Iic s) = ENNReal.ofReal s := by
  have hI : Set.Iic s ∩ Set.Icc 0 1 = Set.Icc 0 s := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans h₁⟩⟩
  rw [Measure.restrict_apply measurableSet_Iic, hI, Real.volume_Icc, sub_zero]

/-- One cluster: both endpoints share the noise `id`. -/
def U1 : Fin 1 → ℝ → ℝ := fun _ => id

/-- The cluster map of the one-cluster family. -/
def c1 : Fin 2 → Fin 1 := fun _ => 0

/-- Exponents: endpoint `0` is a null (`θ = 1`), endpoint `1` has `θ = 2`. -/
def θ12 : Fin 2 → ℝ := ![1, 2]

lemma θ12_pos (j : Fin 2) : 0 < θ12 j := by
  fin_cases j <;> norm_num [θ12]

lemma lehmannPValue_U1_zero (ω : ℝ) : lehmannPValue U1 c1 θ12 0 ω = max ω 0 := by
  simp [lehmannPValue, U1, θ12]

lemma lehmannPValue_U1_one (ω : ℝ) : lehmannPValue U1 c1 θ12 1 ω = max ω 0 ^ 2 := by
  simp [lehmannPValue, U1, θ12]

lemma setOf_max_sq_le {a : ℝ} (ha : 0 ≤ a) : {ω : ℝ | max ω 0 ^ 2 ≤ a ^ 2} = Set.Iic a := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Iic]
  rw [pow_le_pow_iff_left₀ (le_max_right _ _) ha two_ne_zero]
  exact ⟨fun h => (le_max_left _ _).trans h, fun h => max_le h ha⟩

lemma setOf_max_le {a : ℝ} (ha : 0 ≤ a) : {ω : ℝ | max ω 0 ≤ a} = Set.Iic a := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_Iic]
  exact ⟨fun h => (le_max_left _ _).trans h, fun h => max_le h ha⟩

/-- **Power from the definition**: `P(max ω 0 ^ 2 ≤ 1/4) = P(ω ≤ 1/2) = 1/2`. -/
lemma unif_lehmannPValue_one_le : unif {ω | lehmannPValue U1 c1 θ12 1 ω ≤ 1 / 4} =
    ENNReal.ofReal (1 / 2) := by
  have h : {ω | lehmannPValue U1 c1 θ12 1 ω ≤ 1 / 4} = Set.Iic (1 / 2) := by
    simp_rw [lehmannPValue_U1_one, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num]
    exact setOf_max_sq_le (by norm_num)
  rw [h, unif_Iic (by norm_num)]

/-- The exact power formula `t ^ (1 / θ)` agrees with the direct computation:
`(1/4) ^ (1/2) = 1/2`. -/
example : unif {ω | lehmannPValue U1 c1 θ12 1 ω ≤ 1 / 4} =
    ENNReal.ofReal ((1 / 4) ^ (θ12 1)⁻¹) := by
  rw [unif_lehmannPValue_one_le]
  congr 1
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ (θ12 1) by norm_num [θ12, Real.rpow_two],
    Real.rpow_rpow_inv (by norm_num) (θ12_pos 1).ne']

example : unif {ω | lehmannPValue U1 c1 θ12 1 ω ≤ 1 / 4} =
    ENNReal.ofReal ((1 / 4) ^ (θ12 1)⁻¹) :=
  measure_lehmannPValue_le HasLaw.id (θ12_pos 1) (by norm_num) (by norm_num)

/-- **The non-null p-value is not valid**: its power `1/2` at level `1/4` exceeds `1/4`. -/
lemma not_isValidPValue_lehmannPValue_one : ¬ IsValidPValue unif (lehmannPValue U1 c1 θ12 1) := by
  intro h
  have := h (1 / 4) ⟨by norm_num, by norm_num⟩
  rw [unif_lehmannPValue_one_le, ENNReal.ofReal_le_ofReal_iff (by norm_num)] at this
  norm_num at this

/-- Strict unbiasedness, through the theorem. -/
example : ENNReal.ofReal (1 / 4) < unif {ω | lehmannPValue U1 c1 θ12 1 ω ≤ 1 / 4} :=
  ofReal_lt_measure_lehmannPValue_le HasLaw.id (by norm_num [θ12]) (by norm_num) (by norm_num)

/-- The null p-value of the family is valid. -/
example : IsValidPValue unif (lehmannPValue U1 c1 θ12 0) :=
  isValidPValue_lehmannPValue_of_eq_one HasLaw.id (by simp [θ12])

/-- **The two p-values of one cluster are not independent**: `{p₀ ≤ 1/4} = {p₁ ≤ 1/16}`, of
probability `1/4 ≠ 1/16`. -/
lemma not_indepFun_lehmannPValue :
    ¬ IndepFun (lehmannPValue U1 c1 θ12 0) (lehmannPValue U1 c1 θ12 1) unif := by
  intro h
  have hm := h.measure_inter_preimage_eq_mul (Set.Iic (1 / 4)) (Set.Iic (1 / 16))
    measurableSet_Iic measurableSet_Iic
  have h0 : lehmannPValue U1 c1 θ12 0 ⁻¹' Set.Iic (1 / 4) = Set.Iic (1 / 4) := by
    change {ω | lehmannPValue U1 c1 θ12 0 ω ≤ 1 / 4} = _
    simp_rw [lehmannPValue_U1_zero]
    exact setOf_max_le (by norm_num)
  have h1 : lehmannPValue U1 c1 θ12 1 ⁻¹' Set.Iic (1 / 16) = Set.Iic (1 / 4) := by
    change {ω | lehmannPValue U1 c1 θ12 1 ω ≤ 1 / 16} = _
    simp_rw [lehmannPValue_U1_one, show (1 / 16 : ℝ) = (1 / 4) ^ 2 by norm_num]
    exact setOf_max_sq_le (by norm_num)
  rw [h0, h1, Set.inter_self, unif_Iic (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_eq_ofReal_iff (by norm_num)
      (by norm_num)] at hm
  norm_num at hm

/-- The comonotone family is PRDS on every set of endpoints. -/
example (H0 : Finset (Fin 2)) : IsPRDSOn unif (lehmannPValue U1 c1 θ12) H0 :=
  isPRDSOn_lehmannPValue (fun _ => measurable_id) iIndepFun.of_subsingleton c1 θ12_pos H0

/-! ### Two independent clusters -/

/-- Two independent uniforms. -/
noncomputable abbrev unif2 : Measure (Fin 2 → ℝ) := Measure.pi fun _ => unif

/-- The noise of cluster `b` is coordinate `b`. -/
def U2 : Fin 2 → (Fin 2 → ℝ) → ℝ := fun b ω => ω b

lemma hasLaw_U2 (b : Fin 2) : HasLaw (U2 b) (volume.restrict (Set.Icc (0 : ℝ) 1)) unif2 :=
  (measurePreserving_eval (fun _ : Fin 2 => unif) b).hasLaw

lemma iIndepFun_U2 : iIndepFun U2 unif2 :=
  iIndepFun_pi (μ := fun _ => unif) (X := fun _ x => x) fun _ => measurable_id.aemeasurable

/-- The two-cluster family (independent p-values) is PRDS on every set of endpoints. -/
example (H0 : Finset (Fin 2)) : IsPRDSOn unif2 (lehmannPValue U2 id θ12) H0 :=
  isPRDSOn_lehmannPValue (fun b => measurable_pi_apply b) iIndepFun_U2 id θ12_pos H0

/-- Bonferroni power at level `1/10` on the two-cluster family: `(1/20) ^ (1/2)`. -/
example :
    unif2 {ω | (1 : Fin 2) ∈ bonferroniRejections (1 / 10) fun i => lehmannPValue U2 id θ12 i ω} =
    ENNReal.ofReal ((1 / 10 / 2) ^ (θ12 1)⁻¹) :=
  measure_mem_bonferroniRejections_lehmannPValue (hasLaw_U2 1) (θ12_pos 1) (by norm_num)
    (by norm_num)

/-! ### Bonferroni rejections are Holm and BH rejections -/

lemma zero_mem_bonferroniRejections : (0 : Fin 2) ∈ bonferroniRejections (1 / 20) ![0, 1] := by
  norm_num [bonferroniRejections]

example : (0 : Fin 2) ∈ holmRejections (1 / 20) ![0, 1] :=
  bonferroniRejections_subset_holmRejections (by norm_num) _ zero_mem_bonferroniRejections

example : (0 : Fin 2) ∈ bhRejections (1 / 20) ![0, 1] :=
  bonferroniRejections_subset_bhRejections (by norm_num) _ zero_mem_bonferroniRejections

/-! ### A randomized trial on `[0, 1]` -/

/-- Treated units: `ω ≤ 1/2`. -/
def treatedR : Set ℝ := Set.Iic (1 / 2)

/-- Control potential outcomes: `0` for both endpoints. -/
def y0R : Fin 2 → ℝ → ℝ := fun _ _ => 0

/-- Treated potential outcomes: `0` for endpoint `0`, `2` for endpoint `1`. -/
def y1R : Fin 2 → ℝ → ℝ := fun j _ => ![0, 2] j

lemma measurableSet_treatedR : MeasurableSet treatedR := measurableSet_Iic

lemma measurable_y0R (j : Fin 2) : Measurable (y0R j) := measurable_const

lemma measurable_y1R (j : Fin 2) : Measurable (y1R j) := measurable_const

lemma integrable_y0R (j : Fin 2) : Integrable (y0R j) unif := integrable_const _

lemma integrable_y1R (j : Fin 2) : Integrable (y1R j) unif := integrable_const _

lemma unif_real_treatedR : unif.real treatedR = 1 / 2 := by
  rw [measureReal_def, treatedR, unif_Iic (by norm_num), ENNReal.toReal_ofReal]
  norm_num

/-- `ateNulls = {0}`, from the definition. -/
lemma ateNulls_R : ateNulls unif y0R y1R = {0} := by
  ext j
  rw [mem_ateNulls_iff, Finset.mem_singleton]
  fin_cases j <;> simp [y0R, y1R]

lemma stronglyIgnorable_R (j : Fin 2) :
    StronglyIgnorable unif treatedR (fun ω => (y0R j ω, y1R j ω)) (fun _ => ()) := by
  have h : IndepFun (treatedR.indicator (1 : ℝ → ℝ)) (fun ω => (y0R j ω, y1R j ω)) unif :=
    indepFun_const_right _ ((0 : ℝ), ![0, 2] j)
  exact stronglyIgnorable_of_indepFun h (by rw [unif_real_treatedR]; norm_num)
    (by rw [unif_real_treatedR]; norm_num)

lemma ipwContrast_R_one :
    ipwContrast unif treatedR (fun _ => ()) (observed treatedR (y0R 1) (y1R 1)) = 2 := by
  rw [ipwContrast_observed_eq_integral measurableSet_treatedR measurable_const (measurable_y0R 1)
    (measurable_y1R 1) (integrable_y0R 1) (integrable_y1R 1) (stronglyIgnorable_R 1)]
  simp [y0R, y1R]

/-- **BH FDR control on the explicit family**, every hypothesis discharged: the FDR over the
causal nulls `{0}` is at most `q / 2`. -/
example (κ : Fin 2 → ℝ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ∫ ω, falseDiscoveryProportion {0} (bhRejections q fun i =>
        ateLehmannPValue unif treatedR (fun _ => ())
          (fun i => observed treatedR (y0R i) (y1R i)) κ U1 c1 i ω) ∂unif ≤ q * 1 / 2 := by
  have h := integral_falseDiscoveryProportion_bhRejections_ateNulls_ateLehmannPValue_le
    (κ := κ) measurableSet_treatedR measurable_const (fun j _ => measurable_y0R j)
    (fun j _ => measurable_y1R j) (fun j _ => integrable_y0R j) (fun j _ => integrable_y1R j)
    (fun j _ => stronglyIgnorable_R j) (U := U1) (fun _ => HasLaw.id) (fun _ => measurable_id)
    iIndepFun.of_subsingleton c1 q hq₀ hq₁
  rw [ateNulls_R, Finset.card_singleton, Nat.cast_one, show ((2 : ℕ) : ℝ) = 2 by norm_num] at h
  exact h

/-- **Holm FWER control on the explicit family**, every hypothesis discharged. -/
example (κ : Fin 2 → ℝ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) :
    unif {ω | (holmRejections α (fun i => ateLehmannPValue unif treatedR (fun _ => ())
        (fun i => observed treatedR (y0R i) (y1R i)) κ U1 c1 i ω) ∩
          ateNulls unif y0R y1R).Nonempty} ≤ ENNReal.ofReal α :=
  measure_holm_ateNulls_familywiseError_ateLehmannPValue_le measurableSet_treatedR
    measurable_const (fun j _ => measurable_y0R j) (fun j _ => measurable_y1R j)
    (fun j _ => integrable_y0R j) (fun j _ => integrable_y1R j) (fun j _ => stronglyIgnorable_R j)
    (U := U1) (fun _ => HasLaw.id) c1 hα₀ hα₁

/-- **Power of the non-null endpoint in terms of its ATE `2`.** -/
example (κ : Fin 2 → ℝ) {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    unif {ω | ateLehmannPValue unif treatedR (fun _ => ())
        (fun i => observed treatedR (y0R i) (y1R i)) κ U1 c1 1 ω ≤ t} =
      ENNReal.ofReal (t ^ Real.exp (-(κ 1 * 2))) := by
  rw [measure_ateLehmannPValue_observed_le measurableSet_treatedR measurable_const
    (measurable_y0R 1) (measurable_y1R 1) (integrable_y0R 1) (integrable_y1R 1)
    (stronglyIgnorable_R 1) (U := U1) HasLaw.id ht₀ ht₁]
  simp [y0R, y1R]

/-- **BH power lower bound** for the non-null endpoint. -/
example (κ : Fin 2 → ℝ) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) :
    ENNReal.ofReal ((q / 2) ^ Real.exp (-(κ 1 * ∫ ω, (y1R 1 ω - y0R 1 ω) ∂unif))) ≤
      unif {ω | (1 : Fin 2) ∈ bhRejections q fun i => ateLehmannPValue unif treatedR
        (fun _ => ()) (fun i => observed treatedR (y0R i) (y1R i)) κ U1 c1 i ω} := by
  have h := ofReal_le_measure_mem_bhRejections_ateLehmannPValue_observed (κ := κ)
    measurableSet_treatedR measurable_const (measurable_y0R 1) (measurable_y1R 1)
    (integrable_y0R 1) (integrable_y1R 1) (stronglyIgnorable_R 1) (U := U1) (c := c1) HasLaw.id
    hq₀ hq₁
  rw [show ((2 : ℕ) : ℝ) = 2 by norm_num] at h
  exact h

/-- **Consistency**: as the scale grows, BH at level `1/20` rejects the non-null endpoint with
probability tending to `1`. -/
example : Tendsto (fun s : ℝ => unif {ω | (1 : Fin 2) ∈ bhRejections (1 / 20) fun i =>
    ateLehmannPValue unif treatedR (fun _ => ()) (fun i => observed treatedR (y0R i) (y1R i))
      (s • fun _ => 1) U1 c1 i ω}) atTop (𝓝 1) :=
  tendsto_measure_mem_bhRejections_ateLehmannPValue HasLaw.id one_pos
    (by rw [ipwContrast_R_one]; norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Probability.Statistics.MultipleTesting.Adaptive.RandomizedEstimandPower
