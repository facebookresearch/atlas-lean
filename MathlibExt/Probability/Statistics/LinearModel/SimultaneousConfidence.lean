/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.LinearHypothesisF
public import MathlibExt.Probability.Statistics.ConfidenceSet
public import MathlibExt.Probability.Distributions.SnedecorF
public import Mathlib.Probability.HasLaw

/-!
# Simultaneous Scheffe coverage

Inverting the exact `F` test for the linear hypothesis `C β = c` gives a confidence set for
the contrast vector `C β`: for a cutoff `c` whose central `F(q, n - p)` mass on `[0, c]`
reaches `1 - α`, the non-rejected contrast set covers the true contrast with probability at
least `1 - α`. Quantile computation for `c` is outside this file.

## Main results

* `scheffe_coverage`: simultaneous coverage of the inverted `F` test.
-/

@[expose] public section

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory

/- Copied from `LinearModel.LinearHypothesis` (private there; kept private here). The
observation-map measurability helper below needs it. -/
private theorem smul_inv_smul_eq {m : Type*} {σ : ℝ} (hσ : 0 < σ) (e : m → ℝ) :
    σ • σ⁻¹ • e = e := by
  rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]

private theorem scheffe_aemeasurable_model {m k : Type*} [Fintype m] [Fintype k]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (X : Matrix m k ℝ)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω)
      (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    AEMeasurable (fun ω => X *ᵥ β + ε ω) μ := by
  have hφ : Measurable (fun v : m → ℝ => X *ᵥ β + σ • v) := by fun_prop
  have hfg : (fun ω => X *ᵥ β + ε ω)
      = (fun v : m → ℝ => X *ᵥ β + σ • v) ∘ (fun ω => σ⁻¹ • ε ω) := by
    funext ω
    simp only [Function.comp_apply]
    rw [smul_inv_smul_eq hσ]
  rw [hfg]
  exact hφ.comp_aemeasurable hε.aemeasurable

/-- **Simultaneous Scheffe coverage by inverting the `F` test**: under the exact-`F`-law
hypotheses, for a cutoff `c` whose central `F(q, n-p)` mass on `[0, c]` reaches `1 - α`,
the non-rejected contrast set covers the true contrast with probability at least `1 - α`.
The level input is the `F` law at the fiber hypothesis; only the cutoff mass is assumed, and
the rejection sets are measurable by `measurable_fStatistic`. This is simultaneous coverage,
not Scheffe's lemma on `L1` convergence (which lives in `MathlibExt/MeasureTheory/Function`). -/
theorem scheffe_coverage {m k r : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] [Fintype r] [DecidableEq r]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ} {C : Matrix r k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hC : IsUnit (C * (Xᵀ * X)⁻¹ * Cᵀ)) (hr : 0 < Fintype.card r)
    (hkm : Fintype.card k < Fintype.card m)
    (c : ℝ) {α : ℝ}
    (hmass : (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
      (Set.Icc 0 c) ≥ 1 - α)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    1 - α ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | C *ᵥ β ∈ confSetOfTests
        (fun t : r → ℝ => {y : m → ℝ | c < fStatistic X C t y}) y} := by
  obtain ⟨_hα0, _hα1⟩ := hα
  have hR : ∀ t : r → ℝ, MeasurableSet {y : m → ℝ | c < fStatistic X C t y} :=
    fun t => measurableSet_lt measurable_const (measurable_fStatistic X C t)
  have hμ : IsProbabilityMeasure μ := hε.isProbabilityMeasure
  have hP : ∀ β' : k → ℝ, IsProbabilityMeasure (μ.map fun ω => X *ᵥ β' + ε ω) :=
    fun _ => inferInstance
  have hlevel : ∀ β' : k → ℝ, (μ.map fun ω => X *ᵥ β' + ε ω).real
      {y : m → ℝ | c < fStatistic X C (C *ᵥ β') y} ≤ α := by
    intro β'
    have hf : AEMeasurable (fun ω => X *ᵥ β' + ε ω) μ :=
      scheffe_aemeasurable_model X β' hσ hε
    have hR' : MeasurableSet {y : m → ℝ | c < fStatistic X C (C *ᵥ β') y} := hR _
    have hmap : (μ.map fun ω => X *ᵥ β' + ε ω).real
        {y : m → ℝ | c < fStatistic X C (C *ᵥ β') y}
        = μ.real ((fun ω => X *ᵥ β' + ε ω) ⁻¹' {y : m → ℝ | c < fStatistic X C (C *ᵥ β') y}) :=
      map_measureReal_apply_of_aemeasurable hf hR'
    have hpre : (fun ω => X *ᵥ β' + ε ω) ⁻¹' {y : m → ℝ | c < fStatistic X C (C *ᵥ β') y}
        = {ω | c < fStatistic X C (C *ᵥ β') (X *ᵥ β' + ε ω)} := rfl
    rw [hmap, hpre]
    have hF := hasLaw_fStatistic hX hC hr hkm β' (c := C *ᵥ β') rfl hσ hε
    have hmeas : MeasurableSet {v : ℝ | c < v} :=
      measurableSet_lt measurable_const measurable_id
    have heq : μ.real {ω | c < fStatistic X C (C *ᵥ β') (X *ᵥ β' + ε ω)}
        = (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
          {v : ℝ | c < v} :=
      hF.measureReal_eq hmeas
    rw [heq]
    have hFprob := isProbabilityMeasure_snedecorFMeasure hr (Nat.sub_pos_of_lt hkm)
    have hIcc : MeasurableSet (Set.Icc (0 : ℝ) c) := measurableSet_Icc
    have hsub : {v : ℝ | c < v} ⊆ (Set.Icc (0 : ℝ) c)ᶜ := by
      intro v hv
      simp only [Set.mem_ofPred_eq] at hv
      intro hcon
      rw [Set.mem_Icc] at hcon
      linarith
    have hmono : (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
        {v : ℝ | c < v}
        ≤ (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
          (Set.Icc (0 : ℝ) c)ᶜ :=
      measureReal_mono hsub (measure_ne_top _ _)
    have hcompl : (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
        (Set.Icc (0 : ℝ) c)ᶜ
        = 1 - (snedecorFMeasure (Fintype.card r) (Fintype.card m - Fintype.card k)).real
          (Set.Icc (0 : ℝ) c) :=
      probReal_compl_eq_one_sub hIcc
    linarith
  have hcov := (level_iff_coverage
    (fun β' : k → ℝ => μ.map fun ω => X *ᵥ β' + ε ω)
    (fun β' : k → ℝ => C *ᵥ β')
    (fun t : r → ℝ => {y : m → ℝ | c < fStatistic X C t y})
    hR).mp hlevel
  exact hcov β

end MathlibExt.Probability.Statistics.LinearModel
