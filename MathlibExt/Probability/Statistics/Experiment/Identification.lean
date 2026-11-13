/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.CausalIdentification
public import MathlibExt.Probability.Statistics.Identifiability
public import MathlibExt.Probability.Statistics.Experiment.Assignment
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Design-based ATE identification

The complete-randomization observation law over fixed potential-outcome
schedules identifies the ATE.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Causality

namespace MathlibExt.Probability.Statistics.Experiment.Identification

variable {ι : Type*}
variable [Fintype ι]

private lemma sum_powersetCard_ite_mem [DecidableEq ι] (n₁ : ℕ) (i : ι) :
    (∑ S ∈ univ.powersetCard n₁, (if i ∈ S then (1 : ℝ) else 0)) * (Fintype.card ι) =
      (Fintype.card ι).choose n₁ * n₁ := by
  rw [sum_boole]
  rcases Nat.eq_zero_or_pos n₁ with rfl | hn
  · simp
  have hcard := card_filter_powersetCard_subset {i} univ n₁ (by simp) (by simp; omega)
  simp only [singleton_subset_iff, card_singleton, card_univ] at hcard
  rw [hcard]
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ι = N + 1 :=
    ⟨Fintype.card ι - 1, (Nat.succ_pred_eq_of_pos (Fintype.card_pos_iff.2 ⟨i⟩)).symm⟩
  obtain ⟨k, rfl⟩ : ∃ k, n₁ = k + 1 := ⟨n₁ - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  rw [hN]
  simp only [Nat.add_sub_cancel]
  have := Nat.add_one_mul_choose_eq N k
  rw [mul_comm]
  exact_mod_cast this

set_option linter.unusedDecidableInType false in
/-- Design-based ATE identification: under complete randomization with both arms
nonempty, the observation law over fixed potential-outcome schedules identifies
the ATE in the `IsIdentifiedBy` sense. The law equality premise determines the
per-unit outcome means, hence the ATE. The ATE here is byte-identical to the
estimand targeted by `integral_diffInMeans_completeRandomization`. -/
theorem ate_isIdentifiedBy_completeRandomization {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
    {n₁ : ℕ} (h₁ : 1 ≤ n₁) (h₀ : n₁ + 1 ≤ Fintype.card ι) :
    IsIdentifiedBy
      (fun θ : (ι → ℝ) × (ι → ℝ) =>
        obsLaw ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
          {p : ι × Finset ι | p.1 ∈ p.2} Prod.fst
          (fun p => θ.1 p.1) (fun p => θ.2 p.1))
      (fun θ : (ι → ℝ) × (ι → ℝ) => ate θ.1 θ.2) := by
  have hn₁_le : n₁ ≤ Fintype.card ι := by omega
  have hCR : IsProbabilityMeasure (completeRandomization ι n₁) :=
    isProbabilityMeasure_completeRandomization hn₁_le
  have hT₀ : MeasurableSet {p : ι × Finset ι | p.1 ∈ p.2} := MeasurableSet.of_discrete
  have hX₀ : Measurable (Prod.fst : ι × Finset ι → ι) := measurable_fst
  have hU : IsProbabilityMeasure (Measure.uniformOfFinset (Finset.univ : Finset ι)) := by
    constructor
    have hC : ((Finset.univ : Finset ι).card : ENNReal) ≠ 0 := by
      rw [Finset.card_univ]
      have hpos : 0 < Fintype.card ι := by omega
      exact_mod_cast (Nat.pos_iff_ne_zero.1 hpos)
    rw [Measure.uniformOfFinset_apply]
    simp only [Set.mem_univ, Finset.filter_true]
    exact ENNReal.div_self hC (ENNReal.natCast_ne_top _)
  have hY₀ : ∀ θ : (ι → ℝ) × (ι → ℝ), Measurable (fun p : ι × Finset ι => θ.1 p.1) :=
    fun _ => Measurable.of_discrete
  have hY₁ : ∀ θ : (ι → ℝ) × (ι → ℝ), Measurable (fun p : ι × Finset ι => θ.2 p.1) :=
    fun _ => Measurable.of_discrete
  have hY₀i : ∀ θ : (ι → ℝ) × (ι → ℝ),
      Integrable (fun p : ι × Finset ι => θ.1 p.1)
        ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)) :=
    fun _ => Integrable.of_finite
  have hY₁i : ∀ θ : (ι → ℝ) × (ι → ℝ),
      Integrable (fun p : ι × Finset ι => θ.2 p.1)
        ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)) :=
    fun _ => Integrable.of_finite
  have hCI : ∀ θ : (ι → ℝ) × (ι → ℝ), CondIndepDiscrete
      ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
      {p : ι × Finset ι | p.1 ∈ p.2}
      (fun p : ι × Finset ι => (θ.1 p.1, θ.2 p.1))
      Prod.fst := by
    intro θ B _ w
    by_cases hmem : (θ.1 w, θ.2 w) ∈ B
    · have h1 : {p : ι × Finset ι | p.1 ∈ p.2} ∩
          (fun p : ι × Finset ι => (θ.1 p.1, θ.2 p.1)) ⁻¹' B ∩ Prod.fst ⁻¹' {w}
            = {p : ι × Finset ι | p.1 ∈ p.2} ∩ Prod.fst ⁻¹' {w} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨⟨hT, _⟩, hX⟩
          exact ⟨hT, hX⟩
        · rintro ⟨hT, hX⟩
          have heq : (θ.1 p.1, θ.2 p.1) = (θ.1 w, θ.2 w) := by rw [hX]
          exact ⟨⟨hT, heq ▸ hmem⟩, hX⟩
      have h2 : (fun p : ι × Finset ι => (θ.1 p.1, θ.2 p.1)) ⁻¹' B ∩ Prod.fst ⁻¹' {w}
            = Prod.fst ⁻¹' {w} := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · rintro ⟨_, hX⟩
          exact hX
        · intro hX
          have heq : (θ.1 p.1, θ.2 p.1) = (θ.1 w, θ.2 w) := by rw [hX]
          exact ⟨heq ▸ hmem, hX⟩
      rw [h1, h2]
    · have h2 : (fun p : ι × Finset ι => (θ.1 p.1, θ.2 p.1)) ⁻¹' B ∩ Prod.fst ⁻¹' {w}
            = ∅ := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro hB hX
        have heq : (θ.1 p.1, θ.2 p.1) = (θ.1 w, θ.2 w) := by rw [hX]
        exact hmem (heq ▸ hB)
      have h1 : {p : ι × Finset ι | p.1 ∈ p.2} ∩
          (fun p : ι × Finset ι => (θ.1 p.1, θ.2 p.1)) ⁻¹' B ∩ Prod.fst ⁻¹' {w}
            = ∅ := by
        ext p
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
          Set.mem_empty_iff_false, iff_false, not_and]
        intro h hX
        obtain ⟨_, hB⟩ := h
        have heq : (θ.1 p.1, θ.2 p.1) = (θ.1 w, θ.2 w) := by rw [hX]
        exact hmem (heq ▸ hB)
      rw [h1, h2]
      simp
  have hOverlap : ∀ w : ι,
      ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
        (Prod.fst ⁻¹' {w}) ≠ 0 →
        0 < propensity ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
          {p : ι × Finset ι | p.1 ∈ p.2} Prod.fst w ∧
        propensity ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
          {p : ι × Finset ι | p.1 ∈ p.2} Prod.fst w < 1 := by
    intro w _
    have hcount := sum_powersetCard_ite_mem n₁ w
    have hXset : (Prod.fst : ι × Finset ι → ι) ⁻¹' {w} = {w} ×ˢ (Set.univ : Set (Finset ι)) := by
      ext p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_univ, and_true]
    have hTXset : {p : ι × Finset ι | p.1 ∈ p.2} ∩ (Prod.fst : ι × Finset ι → ι) ⁻¹' {w}
        = {w} ×ˢ {S : Finset ι | w ∈ S} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
        Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hT, hX⟩
        exact ⟨hX, hX ▸ hT⟩
      · rintro ⟨hX, hS⟩
        exact ⟨hX ▸ hS, hX⟩
    have hUw : (Measure.uniformOfFinset (Finset.univ : Finset ι)).real {w}
        = (Fintype.card ι : ℝ)⁻¹ := by
      rw [measureReal_def,
        Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_univ w),
        ENNReal.toReal_inv, ENNReal.toReal_natCast, Finset.card_univ]
    have hCcard : (Finset.univ.powersetCard n₁ : Finset (Finset ι)).card
        = (Fintype.card ι).choose n₁ := by
      rw [Finset.card_powersetCard, Finset.card_univ]
    have hCMeas : (completeRandomization ι n₁) {S : Finset ι | w ∈ S}
        = ((@Finset.filter (Finset ι) (fun x => x ∈ {S : Finset ι | w ∈ S})
            (fun x => Classical.propDecidable _) (Finset.univ.powersetCard n₁)).card : ENNReal)
          / ((Fintype.card ι).choose n₁ : ENNReal) := by
      rw [completeRandomization_eq, Measure.uniformOfFinset_apply, hCcard]
    have hFeq : (@Finset.filter (Finset ι) (fun x => x ∈ {S : Finset ι | w ∈ S})
          (fun x => Classical.propDecidable _) (Finset.univ.powersetCard n₁))
        = Finset.filter (fun S => w ∈ S) (Finset.univ.powersetCard n₁) := by
      ext S
      simp
    rw [hFeq] at hCMeas
    have hCReal : (completeRandomization ι n₁).real {S : Finset ι | w ∈ S}
        = (n₁ : ℝ) / (Fintype.card ι : ℝ) := by
      rw [measureReal_def, hCMeas, ENNReal.toReal_div, ENNReal.toReal_natCast,
        ENNReal.toReal_natCast]
      rw [sum_boole] at hcount
      have hNne : (Fintype.card ι : ℝ) ≠ 0 := by
        have hpos : 0 < Fintype.card ι := by omega
        exact_mod_cast (Nat.pos_iff_ne_zero.1 hpos)
      have hCne : ((Fintype.card ι).choose n₁ : ℝ) ≠ 0 := by
        have hpos : 0 < (Fintype.card ι).choose n₁ := Nat.choose_pos hn₁_le
        exact_mod_cast (Nat.pos_iff_ne_zero.1 hpos)
      rw [div_eq_div_iff hCne hNne]
      linear_combination hcount
    have hProdX : (((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)).real
          ((Prod.fst : ι × Finset ι → ι) ⁻¹' {w}))
        = (Fintype.card ι : ℝ)⁻¹ := by
      rw [hXset, measureReal_prod_prod, hUw, probReal_univ, mul_one]
    have hProdTX : (((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)).real
          ({p : ι × Finset ι | p.1 ∈ p.2} ∩ (Prod.fst : ι × Finset ι → ι) ⁻¹' {w}))
        = (Fintype.card ι : ℝ)⁻¹ * ((n₁ : ℝ) / (Fintype.card ι : ℝ)) := by
      rw [hTXset, measureReal_prod_prod, hUw, hCReal]
    have hProp : propensity
          ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
          {p : ι × Finset ι | p.1 ∈ p.2} Prod.fst w
        = (n₁ : ℝ) / (Fintype.card ι : ℝ) := by
      rw [propensity, hProdTX, hProdX]
      have hNne : (Fintype.card ι : ℝ) ≠ 0 := by
        have hpos : 0 < Fintype.card ι := by omega
        exact_mod_cast (Nat.pos_iff_ne_zero.1 hpos)
      have hNinv : (Fintype.card ι : ℝ)⁻¹ ≠ 0 := inv_ne_zero hNne
      field_simp
    rw [hProp]
    have hNpos : (0:ℝ) < (Fintype.card ι : ℝ) := by
      have hpos : 0 < Fintype.card ι := by omega
      exact_mod_cast hpos
    have hn₁pos : (0:ℝ) < (n₁ : ℝ) := by
      have hpos : 0 < n₁ := by omega
      exact_mod_cast hpos
    have hn₁lt : (n₁ : ℝ) < (Fintype.card ι : ℝ) := by
      have hlt : n₁ < Fintype.card ι := by omega
      exact_mod_cast hlt
    constructor
    · exact div_pos hn₁pos hNpos
    · rw [div_lt_one hNpos]
      exact hn₁lt
  have hSI : ∀ θ : (ι → ℝ) × (ι → ℝ), StronglyIgnorable
      ((Measure.uniformOfFinset (Finset.univ : Finset ι)).prod (completeRandomization ι n₁))
      {p : ι × Finset ι | p.1 ∈ p.2}
      (fun p : ι × Finset ι => (θ.1 p.1, θ.2 p.1))
      Prod.fst :=
    fun θ => ⟨hCI θ, hOverlap⟩
  have hProb : ∀ θ : (ι → ℝ) × (ι → ℝ), IsProbabilityMeasure
      ((Measure.uniformOfFinset (Finset.univ : Finset ι)).prod (completeRandomization ι n₁)) :=
    fun _ => inferInstance
  have hBridge : IsIdentifiedBy
      (fun θ : (ι → ℝ) × (ι → ℝ) =>
        obsLaw ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))
          {p : ι × Finset ι | p.1 ∈ p.2} Prod.fst
          (fun p => θ.1 p.1) (fun p => θ.2 p.1))
      (fun θ : (ι → ℝ) × (ι → ℝ) =>
        ∫ ω, ((fun p : ι × Finset ι => θ.2 p.1) ω - (fun p : ι × Finset ι => θ.1 p.1) ω)
          ∂((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁))) :=
    ate_isIdentifiedBy_observational_law
      (fun _ => hT₀) (fun _ => hX₀) hY₀ hY₁ hY₀i hY₁i hSI
  have hInt : ∀ θ : (ι → ℝ) × (ι → ℝ),
      (∫ ω, ((fun p : ι × Finset ι => θ.2 p.1) ω - (fun p : ι × Finset ι => θ.1 p.1) ω)
        ∂((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)))
      = ate θ.1 θ.2 := by
    intro θ
    have hIntble : Integrable (fun p : ι × Finset ι => θ.2 p.1 - θ.1 p.1)
        ((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)) :=
      (hY₁i θ).sub (hY₀i θ)
    change (∫ ω, (θ.2 ω.1 - θ.1 ω.1)
        ∂((Measure.uniformOfFinset Finset.univ).prod (completeRandomization ι n₁)))
      = ate θ.1 θ.2
    rw [integral_prod _ hIntble]
    have hInner : ∀ i : ι, (∫ S, (θ.2 i - θ.1 i) ∂(completeRandomization ι n₁))
        = θ.2 i - θ.1 i := by
      intro i
      rw [integral_const, probReal_univ, one_smul]
    change (∫ i, (∫ S, (θ.2 i - θ.1 i) ∂(completeRandomization ι n₁))
        ∂(Measure.uniformOfFinset Finset.univ)) = ate θ.1 θ.2
    simp only [hInner]
    have hC : ((Finset.univ : Finset ι).card : ENNReal) ≠ 0 := by
      rw [Finset.card_univ]
      have hpos : 0 < Fintype.card ι := by omega
      exact_mod_cast (Nat.pos_iff_ne_zero.1 hpos)
    rw [Measure.uniformOfFinset,
      integral_finsetSum_measure fun i _ =>
        (Integrable.of_finite :
            Integrable (fun i : ι => θ.2 i - θ.1 i) (Measure.dirac i)).smul_measure
          (ENNReal.inv_ne_top.2 hC)]
    simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      smul_eq_mul, ← mul_sum, Finset.card_univ, popMean, ate]
    ring
  intro θ θ' hObs
  have hI := hBridge θ θ' hObs
  calc ate θ.1 θ.2 = _ := (hInt θ).symm
    _ = _ := hI
    _ = ate θ'.1 θ'.2 := hInt θ'

end MathlibExt.Probability.Statistics.Experiment.Identification
