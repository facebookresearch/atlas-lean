/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Inference
public import MathlibExt.Probability.Statistics.ConfidenceSet
public import MathlibExt.Probability.Distributions.StudentT
public import Mathlib.Probability.HasLaw

/-!
# Exact contrast `t` intervals and the one-sample specialization

Under the contrast `t`-law hypotheses, inverting the two-sided `t` test at an abstract
threshold `c` gives pointwise coverage for a fixed contrast (uniform in the true
coefficient vector `β`); projecting yields the usual interval for `a^T beta`.
In the intercept-only case this is the one-sample `t`
interval, which covers the mean with probability at least `1 - alpha` when the `t_{n-1}`
central mass on `[-c, c]` reaches `1 - alpha`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory ProbabilityTheory Real

private theorem one_sample_coverage_aux {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal}
    (hv : v ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (n - 1)).real (Set.Icc (-c) c) ≥ 1 - α)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    1 - α ≤ P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsqrt_n : (0 : ℝ) < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hTmeas : Measurable (fun x : Fin n → ℝ => √(n : ℝ) * ((∑ i, x i) / n - μ) /
      √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1))) := by fun_prop
  have hY : MeasurePreserving (fun x : Fin n → ℝ => √(n : ℝ) * ((∑ i, x i) / n - μ) /
      √((∑ i, (x i - (∑ j, x j) / n) ^ 2) / ((n : ℝ) - 1)))
      (Measure.pi fun _ : Fin n => gaussianReal μ v) (studentTMeasure (n - 1)) :=
    ⟨hTmeas, map_tStatistic_pi_gaussianReal hn μ hv⟩
  have hT : HasLaw (fun ω : Ω => √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)))
      (studentTMeasure (n - 1)) P :=
    hY.fun_comp_hasLaw hX
  have hEq : P.real {ω | |√(n : ℝ) * ((∑ i, X ω i) / n - μ) /
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))| ≤ c} =
      (studentTMeasure (n - 1)).real (Set.Icc (-c) c) := by
    rw [hT.measureReal_eq (p := fun t => |t| ≤ c)
      (measurableSet_le (by fun_prop) measurable_const)]
    congr 1
    ext t
    simp [abs_le]
  have hsub : {ω | |√(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))| ≤ c} ⊆
        {ω | |(∑ i, X ω i) / n - μ| ≤ c *
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} ∪
        {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω
    by_cases hs : √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0
    · exact Or.inr hs
    · refine Or.inl ?_
      simp only [Set.mem_ofPred_eq]
      have hSpos : 0 < √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (fun h => hs h.symm)
      rw [abs_div, abs_mul, abs_of_pos hsqrt_n, abs_of_pos hSpos] at hω
      have h1 : √(n : ℝ) * |(∑ i, X ω i) / n - μ| ≤
          c * √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) :=
        (div_le_iff₀ hSpos).mp hω
      have h2 : |(∑ i, X ω i) / n - μ| * √(n : ℝ) ≤
          c * √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) := by
        rw [mul_comm]; exact h1
      exact (le_div_iff₀ hsqrt_n).mpr h2
  have hS0 : P.real
      {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} = 0 := by
    have hsub0 : {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} ⊆
        {ω | √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rw [hω, div_zero]
    have hEq0 : P.real {ω | √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} =
        (studentTMeasure (n - 1)).real {t | t = 0} :=
      hT.measureReal_eq (p := fun t => t = 0) (by
        show MeasurableSet {t : ℝ | t = 0}
        rw [Set.ofPred_eq_eq_singleton]
        exact measurableSet_singleton 0)
    have hnull : (studentTMeasure (n - 1)).real {t : ℝ | t = 0} = 0 := by
      have hs : MeasurableSet {t : ℝ | t = 0} := by
        rw [Set.ofPred_eq_eq_singleton]
        exact measurableSet_singleton 0
      have hvol : volume {t : ℝ | t = 0} = 0 := by
        rw [Set.ofPred_eq_eq_singleton]
        exact Real.volume_singleton
      rw [studentTMeasure, measureReal_def, withDensity_apply _ hs,
        setLIntegral_measure_zero _ _ hvol, ENNReal.toReal_zero]
    have : IsProbabilityMeasure P := hX.isProbabilityMeasure
    have hle0 : P.real
        {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} ≤
        P.real {ω | √(n : ℝ) * ((∑ i, X ω i) / n - μ) /
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} :=
      measureReal_mono hsub0 (measure_ne_top _ _)
    rw [hEq0, hnull] at hle0
    exact le_antisymm hle0 measureReal_nonneg
  have : IsProbabilityMeasure P := hX.isProbabilityMeasure
  calc 1 - α ≤ (studentTMeasure (n - 1)).real (Set.Icc (-c) c) := hmass
    _ = P.real {ω | |√(n : ℝ) * ((∑ i, X ω i) / n - μ) /
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1))| ≤ c} := hEq.symm
    _ ≤ P.real ({ω | |(∑ i, X ω i) / n - μ| ≤ c *
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} ∪
        {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
          √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} +
        P.real {ω | √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) = 0} :=
      measureReal_union_le _ _
    _ = P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
        √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} := by
      rw [hS0, add_zero]

set_option linter.unusedVariables false in
/-- **One-sample `t` interval with exact coverage**: for an i.i.d. `N(mu, v)` sample with
`n ≥ 2` and `v ≠ 0`, for `c` whose `t_{n-1}` central mass on `[-c, c]` reaches `1 - alpha`,
the interval `xbar ± c * S / sqrt n` covers `mu` with probability at least `1 - alpha`. -/
theorem one_sample_t_interval_coverage {n : ℕ} (hn : 2 ≤ n) (μ : ℝ) {v : NNReal} (hv : v ≠ 0)
    (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (n - 1)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Fin n → ℝ}
    (hX : HasLaw X (Measure.pi fun _ : Fin n => gaussianReal μ v) P) :
    1 - α ≤ P.real {ω | |(∑ i, X ω i) / n - μ| ≤ c *
      √((∑ i, (X ω i - (∑ j, X ω j) / n) ^ 2) / ((n : ℝ) - 1)) / √(n : ℝ)} := by
  exact one_sample_coverage_aux hn μ hv c hmass hX

end ProbabilityTheory

namespace MathlibExt.Probability.Statistics.LinearModel

open Matrix MeasureTheory ProbabilityTheory

/- Copied from `LinearModel.Inference` (private there; kept private here). The slab
measurability helper below needs it. -/
private theorem smul_inv_smul_eq {m : Type*} {σ : ℝ} (hσ : 0 < σ) (e : m → ℝ) :
    σ • σ⁻¹ • e = e := by
  rw [smul_smul, mul_inv_cancel₀ hσ.ne', one_smul]

/-! ===== Private helpers for the slab and interval proofs. -/

private theorem slab_measurable_mulVec {p q : Type*} [Fintype p]
    (M : Matrix q p ℝ) : Measurable (fun y : p → ℝ => M *ᵥ y) := by
  classical
  unfold Matrix.mulVec dotProduct
  exact Measurable.of_eval fun r => Finset.measurable_sum _ fun c _ =>
    measurable_const.mul (measurable_pi_apply c)

private theorem slab_measurable_mulVec_comp {p q : Type*} [Fintype p]
    {Ω : Type*} [MeasurableSpace Ω] (M : Matrix q p ℝ) {f : Ω → p → ℝ}
    (hf : Measurable f) : Measurable (fun ω => M *ᵥ f ω) :=
  (slab_measurable_mulVec M).comp hf

private theorem slab_measurable_const_dotProduct {p : Type*} [Fintype p]
    {Ω : Type*} [MeasurableSpace Ω] (a : p → ℝ) {f : Ω → p → ℝ}
    (hf : Measurable f) : Measurable (fun ω => a ⬝ᵥ f ω) := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp hf)

private theorem slab_measurable_dotProduct {p : Type*} [Fintype p]
    {Ω : Type*} [MeasurableSpace Ω] {f g : Ω → p → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => f ω ⬝ᵥ g ω) := by
  unfold dotProduct
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hf).mul ((measurable_pi_apply i).comp hg)

private theorem slab_measurable_tStatistic {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] (X : Matrix m k ℝ) (a β : k → ℝ) :
    Measurable (fun y : m → ℝ => tStatistic X a β y) := by
  unfold tStatistic olsEstimator
  have hBH : Measurable (fun y : m → ℝ => olsMatrix X *ᵥ y) :=
    slab_measurable_mulVec _
  have hnum : Measurable (fun y : m → ℝ => a ⬝ᵥ (olsMatrix X *ᵥ y - β)) :=
    slab_measurable_const_dotProduct a (hBH.sub measurable_const)
  have hres : Measurable (fun y : m → ℝ => y - X *ᵥ olsMatrix X *ᵥ y) :=
    measurable_id.sub (slab_measurable_mulVec_comp X hBH)
  have hrss : Measurable (fun y : m → ℝ =>
      (y - X *ᵥ olsMatrix X *ᵥ y) ⬝ᵥ (y - X *ᵥ olsMatrix X *ᵥ y)) :=
    slab_measurable_dotProduct hres hres
  exact hnum.div (((hrss.div_const _).mul_const _).sqrt)

private theorem slab_measurable_rss {m k : Type*} [Fintype m] [DecidableEq m]
    [Fintype k] [DecidableEq k] (X : Matrix m k ℝ) : Measurable (fun y : m → ℝ =>
      (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) := by
  unfold olsEstimator
  have hBH : Measurable (fun y : m → ℝ => olsMatrix X *ᵥ y) :=
    slab_measurable_mulVec _
  have hres : Measurable (fun y : m → ℝ => y - X *ᵥ olsMatrix X *ᵥ y) :=
    measurable_id.sub (slab_measurable_mulVec_comp X hBH)
  exact slab_measurable_dotProduct hres hres

private theorem slab_aemeasurable_model {m k : Type*} [Fintype m] [Fintype k]
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
set_option linter.unusedVariables false in
/-- **Exact slab coverage by inverting the contrast `t` test**: under the `t`-law hypotheses,
for `c` whose `t_{n-p}` central mass on `[-c, c]` reaches `1 - alpha`, the non-rejected
parameter set has coverage at least `1 - alpha`. Proved by pushing the `t` law forward along
the observation map and identifying the coverage-event mass with the `t_{n-p}` central mass
via the pushforward measure identity. -/
theorem contrast_slab_coverage {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    1 - α ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | |tStatistic X a β y| ≤ c} := by
  have hT : HasLaw (fun ω => tStatistic X a β (X *ᵥ β + ε ω))
      (studentTMeasure (Fintype.card m - Fintype.card k)) μ :=
    hasLaw_tStatistic hX hkm β hσ hε ha
  have hmeasT : Measurable (fun y : m → ℝ => tStatistic X a β y) :=
    slab_measurable_tStatistic X a β
  have hf : AEMeasurable (fun ω => X *ᵥ β + ε ω) μ :=
    slab_aemeasurable_model X β hσ hε
  have hmapT : (μ.map fun ω => X *ᵥ β + ε ω).map
        (fun y : m → ℝ => tStatistic X a β y)
      = studentTMeasure (Fintype.card m - Fintype.card k) := by
    have hmm : (μ.map fun ω => X *ᵥ β + ε ω).map
          (fun y : m → ℝ => tStatistic X a β y)
        = μ.map ((fun y : m → ℝ => tStatistic X a β y) ∘
          (fun ω => X *ᵥ β + ε ω)) :=
      AEMeasurable.map_map_of_aemeasurable hmeasT.aemeasurable hf
    rw [hmm]
    exact hT.map_eq
  have hHas : HasLaw (fun y : m → ℝ => tStatistic X a β y)
      (studentTMeasure (Fintype.card m - Fintype.card k))
      (μ.map fun ω => X *ᵥ β + ε ω) :=
    ⟨hmeasT.aemeasurable, hmapT⟩
  have hmeas : MeasurableSet {t : ℝ | |t| ≤ c} :=
    measurableSet_le (by fun_prop) measurable_const
  have heq : (μ.map fun ω => X *ᵥ β + ε ω).real
        {y : m → ℝ | |tStatistic X a β y| ≤ c}
      = (studentTMeasure (Fintype.card m - Fintype.card k)).real
        {t : ℝ | |t| ≤ c} :=
    hHas.measureReal_eq (p := fun t => |t| ≤ c) hmeas
  have hIcc : {t : ℝ | |t| ≤ c} = Set.Icc (-c) c := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, abs_le]
  rw [heq, hIcc]
  exact hmass

set_option linter.unusedVariables false in
/-- **Exact contrast interval**: the projection of the slab onto the contrast value,
`a^T beta` lies in `a^T bh +- c * s` with coverage at least `1 - alpha`, where
`s^2 = (RSS / (n - p)) * contrastVariance`. -/
theorem contrast_interval_coverage {m k : Type*} [Fintype m] [DecidableEq m] [Fintype k]
    [DecidableEq k] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Matrix m k ℝ}
    (hX : IsUnit (Xᵀ * X)) (hkm : Fintype.card k < Fintype.card m)
    {a : k → ℝ} (ha : a ≠ 0) (c : ℝ) {α : ℝ}
    (hmass : (studentTMeasure (Fintype.card m - Fintype.card k)).real (Set.Icc (-c) c) ≥ 1 - α)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (β : k → ℝ) {ε : Ω → m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hε : HasLaw (fun ω => σ⁻¹ • ε ω) (Measure.pi fun _ : m => gaussianReal 0 1) μ) :
    1 - α ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
      {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
        √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
          ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)} := by
  have hq : 0 < contrastVariance X a := contrastVariance_pos hX ha
  have hnpos : 0 < Fintype.card m - Fintype.card k := by omega
  have hdd : (0 : ℝ) < ((Fintype.card m - Fintype.card k : ℕ) : ℝ) :=
    Nat.cast_pos.mpr hnpos
  have hσ2 : (0 : ℝ) < σ ^ 2 := pow_pos hσ 2
  have hf : AEMeasurable (fun ω => X *ᵥ β + ε ω) μ :=
    slab_aemeasurable_model X β hσ hε
  have hSlab := contrast_slab_coverage hX hkm ha c hmass hα β hσ hε
  have hrss_nn : ∀ y : m → ℝ,
      0 ≤ (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y) := by
    intro y
    unfold dotProduct
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hsub : {y : m → ℝ | |tStatistic X a β y| ≤ c} ⊆
      {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
        √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
          ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)}
      ∪ {y : m → ℝ | (y - X *ᵥ olsEstimator X y) ⬝ᵥ
        (y - X *ᵥ olsEstimator X y) = 0} := by
    intro y hy
    rw [Set.mem_union]
    simp only [Set.mem_ofPred_eq] at hy
    by_cases hZ : (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y) = 0
    · exact Or.inr hZ
    · refine Or.inl ?_
      have hRSSpos : (0 : ℝ) <
          (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y) :=
        lt_of_le_of_ne' (hrss_nn y) hZ
      have hDpos : (0 : ℝ) < √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ
            (y - X *ᵥ olsEstimator X y)) /
            ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a) := by
        rw [Real.sqrt_pos]
        exact mul_pos (div_pos hRSSpos hdd) hq
      have hTeq : tStatistic X a β y
          = a ⬝ᵥ (olsEstimator X y - β) / √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ
              (y - X *ᵥ olsEstimator X y)) / ((Fintype.card m - Fintype.card k : ℕ) : ℝ) *
              contrastVariance X a) := rfl
      rw [hTeq, abs_div, abs_of_pos hDpos] at hy
      have hN : a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y
          = -(a ⬝ᵥ (olsEstimator X y - β)) := by
        rw [dotProduct_sub]
        ring
      simp only [Set.mem_ofPred_eq]
      rw [hN, abs_neg]
      exact (div_le_iff₀ hDpos).mp hy
  have hV : HasLaw (fun ω => (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
      (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2)
      (chiSquareMeasure (Fintype.card m - Fintype.card k)) μ :=
    hasLaw_rss_div_sq hX hkm β σ hσ hε
  have hmeasRSS : Measurable (fun y : m → ℝ =>
      (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) :=
    slab_measurable_rss X
  have hZ : (μ.map fun ω => X *ᵥ β + ε ω)
      {y : m → ℝ | (y - X *ᵥ olsEstimator X y) ⬝ᵥ
        (y - X *ᵥ olsEstimator X y) = 0} = 0 := by
    have hpre : {y : m → ℝ | (y - X *ᵥ olsEstimator X y) ⬝ᵥ
          (y - X *ᵥ olsEstimator X y) = 0}
        = (fun y : m → ℝ => (y - X *ᵥ olsEstimator X y) ⬝ᵥ
          (y - X *ᵥ olsEstimator X y)) ⁻¹' {0} := rfl
    rw [hpre, ← Measure.map_apply hmeasRSS (measurableSet_singleton 0)]
    have hcomp1 : ((μ.map fun ω => X *ᵥ β + ε ω).map fun y : m → ℝ =>
          (y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y))
        = μ.map ((fun y : m → ℝ => (y - X *ᵥ olsEstimator X y) ⬝ᵥ
          (y - X *ᵥ olsEstimator X y)) ∘ (fun ω => X *ᵥ β + ε ω)) :=
      AEMeasurable.map_map_of_aemeasurable hmeasRSS.aemeasurable hf
    rw [hcomp1]
    have hdecomp : ((fun y : m → ℝ => (y - X *ᵥ olsEstimator X y) ⬝ᵥ
            (y - X *ᵥ olsEstimator X y)) ∘ (fun ω => X *ᵥ β + ε ω))
        = (fun v : ℝ => σ ^ 2 * v) ∘ (fun ω =>
          (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
            (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2) := by
      funext ω
      simp only [Function.comp_apply]
      show (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
          (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω))
        = σ ^ 2 * (((X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
          (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω))) / σ ^ 2)
      rw [mul_comm (σ ^ 2)]
      exact (div_mul_cancel₀ _ hσ2.ne').symm
    have hψ : Measurable (fun v : ℝ => σ ^ 2 * v) := measurable_const_mul _
    have hcomp2 : (μ.map fun ω => (X *ᵥ β + ε ω -
            X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
            (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2).map
          (fun v : ℝ => σ ^ 2 * v)
        = μ.map ((fun v : ℝ => σ ^ 2 * v) ∘ (fun ω =>
          (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) ⬝ᵥ
            (X *ᵥ β + ε ω - X *ᵥ olsEstimator X (X *ᵥ β + ε ω)) / σ ^ 2)) :=
      AEMeasurable.map_map_of_aemeasurable hψ.aemeasurable hV.aemeasurable
    rw [hdecomp, ← hcomp2, hV.map_eq,
      Measure.map_apply hψ (measurableSet_singleton 0)]
    have hpre0 : (fun v : ℝ => σ ^ 2 * v) ⁻¹' ({0} : Set ℝ) = {0} := by
      ext v
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h1 | h1
        · exact absurd h1 hσ2.ne'
        · exact h1
      · intro h
        rw [h, mul_zero]
    rw [hpre0]
    exact withDensity_absolutelyContinuous _ _
      (Real.volume_singleton (a := (0 : ℝ)))
  have hle : (μ.map fun ω => X *ᵥ β + ε ω) {y : m → ℝ | |tStatistic X a β y| ≤ c}
      ≤ (μ.map fun ω => X *ᵥ β + ε ω)
        {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
          √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
            ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)} := by
    calc (μ.map fun ω => X *ᵥ β + ε ω) {y : m → ℝ | |tStatistic X a β y| ≤ c}
        ≤ (μ.map fun ω => X *ᵥ β + ε ω)
          ({y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
            √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
              ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)}
          ∪ {y : m → ℝ | (y - X *ᵥ olsEstimator X y) ⬝ᵥ
            (y - X *ᵥ olsEstimator X y) = 0}) :=
          measure_mono hsub
      _ ≤ (μ.map fun ω => X *ᵥ β + ε ω)
            {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
              √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
                ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)}
          + (μ.map fun ω => X *ᵥ β + ε ω)
            {y : m → ℝ | (y - X *ᵥ olsEstimator X y) ⬝ᵥ
              (y - X *ᵥ olsEstimator X y) = 0} :=
          measure_union_le _ _
      _ = (μ.map fun ω => X *ᵥ β + ε ω)
          {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
            √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
              ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)} := by
          rw [hZ, add_zero]
  have hP : IsProbabilityMeasure (μ.map fun ω => X *ᵥ β + ε ω) := by
    have hφ : Measurable (fun v : m → ℝ => X *ᵥ β + σ • v) := by fun_prop
    have hfg : (fun ω => X *ᵥ β + ε ω)
        = (fun v : m → ℝ => X *ᵥ β + σ • v) ∘ (fun ω => σ⁻¹ • ε ω) := by
      funext ω
      simp only [Function.comp_apply]
      rw [smul_inv_smul_eq hσ]
    have hmapfg : (μ.map fun ω => σ⁻¹ • ε ω).map
          (fun v : m → ℝ => X *ᵥ β + σ • v)
        = μ.map ((fun v : m → ℝ => X *ᵥ β + σ • v) ∘ (fun ω => σ⁻¹ • ε ω)) :=
      AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable hε.aemeasurable
    rw [hfg, ← hmapfg, hε.map_eq]
    refine ⟨?_⟩
    rw [Measure.map_apply hφ MeasurableSet.univ, Set.preimage_univ, measure_univ]
  have hfin : (μ.map fun ω => X *ᵥ β + ε ω)
      {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
        √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
          ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)} ≠ ⊤ := by
    exact ne_top_of_le_ne_top (b := 1) (by simp)
      (calc (μ.map fun ω => X *ᵥ β + ε ω) _
          ≤ (μ.map fun ω => X *ᵥ β + ε ω) Set.univ :=
            measure_mono (Set.subset_univ _)
        _ = 1 := hP.measure_univ)
  have hreal : (μ.map fun ω => X *ᵥ β + ε ω).real
        {y : m → ℝ | |tStatistic X a β y| ≤ c}
      ≤ (μ.map fun ω => X *ᵥ β + ε ω).real
        {y : m → ℝ | |a ⬝ᵥ β - a ⬝ᵥ olsEstimator X y| ≤ c *
          √(((y - X *ᵥ olsEstimator X y) ⬝ᵥ (y - X *ᵥ olsEstimator X y)) /
            ((Fintype.card m - Fintype.card k : ℕ) : ℝ) * contrastVariance X a)} :=
    ENNReal.toReal_mono hfin hle
  exact hSlab.trans hreal

end MathlibExt.Probability.Statistics.LinearModel
