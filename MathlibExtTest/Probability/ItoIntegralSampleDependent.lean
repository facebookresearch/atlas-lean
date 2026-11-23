/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.ItoIntegralProperties

/-!
# A sample-dependent elementary Itô-integrand fixture

This module supplies the shared fixture used by the algebraic and continuous-modification tests.
The bounded coefficient is the sign selected by `B 1`, and the processes place that coefficient in
adjacent time windows `(1, 2]` and `(2, 3]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal ProbabilityTheory

namespace MathlibExtTest.Probability.ItoIntegralSampleDependent

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- A bounded coefficient determined by the sign of `B 1`. -/
noncomputable def brownianSign (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ :=
  if B 1 ω ≤ 0 then 1 else -1

/-- The Brownian-sign coefficient is measurable at time `1`. -/
theorem brownianSign_measurable (hBF : Adapted F B) :
    Measurable[F 1] (brownianSign B) :=
  Measurable.ite (measurableSet_le (hBF 1) measurable_const) measurable_const measurable_const

/-- The Brownian-sign coefficient has absolute value one. -/
theorem abs_brownianSign (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    |brownianSign B ω| = 1 := by
  unfold brownianSign
  split <;> norm_num

/-- The Brownian-sign coefficient restricted to the elementary time window `(a, b]`. -/
noncomputable def signedWindow (B : ℝ≥0 → Ω → ℝ) (a b : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun u ω ↦ (Set.Ioc a b).indicator (fun _ ↦ brownianSign B ω) u

/-- A signed window beginning no earlier than time `1` is progressive. -/
theorem signedWindow_progressive (hBF : Adapted F B) (a b : ℝ≥0)
    (h1a : (1 : ℝ≥0) ≤ a) : IsProgressive F (signedWindow B a b) := by
  intro T
  by_cases haT : a ≤ T
  · exact Measurable.indicator
      (((brownianSign_measurable hBF).mono (F.mono (h1a.trans haT)) le_rfl).comp measurable_snd)
      (measurableSet_Ioc.preimage (measurable_subtype_coe.comp measurable_fst))
  · have hz : (fun p : Set.Iic T × Ω ↦ signedWindow B a b p.1 p.2) = 0 := by
      funext p
      change (Set.Ioc a b).indicator (fun _ ↦ brownianSign B p.2) p.1 = 0
      rw [Set.indicator_of_notMem]
      exact fun (hp : (p.1 : ℝ≥0) ∈ Set.Ioc a b) ↦
        haT (hp.1.le.trans p.1.property)
    rw [hz]
    exact measurable_const

private theorem indicator_toNNReal (a b : ℝ≥0) (c u : ℝ) :
    (Set.Ioc a b).indicator (fun _ ↦ c) u.toNNReal =
      (Set.Ioc (a : ℝ) b).indicator (fun _ ↦ c) u := by
  by_cases hu : 0 ≤ u
  · have hmem : u.toNNReal ∈ Set.Ioc a b ↔ u ∈ Set.Ioc (a : ℝ) b := by
      rw [Set.mem_Ioc, Set.mem_Ioc, ← NNReal.coe_lt_coe, ← NNReal.coe_le_coe,
        Real.coe_toNNReal _ hu]
    by_cases h : u ∈ Set.Ioc (a : ℝ) b
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hmem.mp h)]
  · push Not at hu
    have h1 : u ∉ Set.Ioc (a : ℝ) b := fun h ↦ by linarith [h.1, NNReal.coe_nonneg a]
    have h2 : u.toNNReal ∉ Set.Ioc a b := by
      rw [Real.toNNReal_of_nonpos hu.le]
      simp
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

private noncomputable def signedDifference (F : Filtration ℝ≥0 mΩ)
    (B : ℝ≥0 → Ω → ℝ) (hBF : Adapted F B) : ElementaryIntegrand F where
  n := 2
  time := ![1, 2, 3]
  monotone_time := by
    refine Fin.monotone_iff_le_succ.mpr fun i ↦ ?_
    fin_cases i <;> norm_num
  coeff := ![brownianSign B, fun ω ↦ -brownianSign B ω]
  measurable_coeff := by
    intro i
    fin_cases i
    · exact brownianSign_measurable hBF
    · exact ((brownianSign_measurable hBF).mono (F.mono (by norm_num)) le_rfl).neg
  bound := 1
  abs_coeff_le := by
    intro i ω
    fin_cases i <;> simp [abs_brownianSign]

private theorem signedDifference_toProcess (hBF : Adapted F B) :
    (signedDifference F B hBF).toProcess =
      signedWindow B 1 2 - signedWindow B 2 3 := by
  funext u ω
  unfold ElementaryIntegrand.toProcess
  change
    (∑ i : Fin 2,
      (Set.Ioc
        ((![(1 : ℝ≥0), 2, 3] : Fin 3 → ℝ≥0) i.castSucc)
        ((![(1 : ℝ≥0), 2, 3] : Fin 3 → ℝ≥0) i.succ)).indicator
        (fun _ ↦ (![brownianSign B, fun ω ↦ -brownianSign B ω] : Fin 2 → Ω → ℝ) i ω) u) =
      signedWindow B 1 2 u ω - signedWindow B 2 3 u ω
  rw [Fin.sum_univ_two]
  by_cases hu : u ∈ Set.Ioc (2 : ℝ≥0) 3 <;>
    simp [signedWindow, hu, sub_eq_add_neg]

private theorem elementary_energy_ne_top [IsFiniteMeasure P] (K : ElementaryIntegrand F)
    (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ‖K.toProcess u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
  let Z : ElementaryIntegrand F :=
    ElementaryIntegrand.single 0 0 le_rfl (fun _ ↦ (0 : ℝ)) measurable_const 0 (by simp)
  have hZ : Z.toProcess = fun _ _ ↦ 0 := by
    dsimp [Z]
    rw [ElementaryIntegrand.toProcess_single]
    funext u ω
    simp
  have h := K.integrandDist_ne_top (P := P) Z t
  rw [hZ] at h
  simpa [integrandDist] using h

/-- A Brownian-sign window has finite energy on every finite horizon. -/
theorem signedWindow_energy_ne_top [IsFiniteMeasure P] (hBF : Adapted F B)
    (a b : ℝ≥0) (h1a : (1 : ℝ≥0) ≤ a) (hab : a ≤ b) (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖signedWindow B a b u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
  let K := ElementaryIntegrand.single a b hab (brownianSign B)
    ((brownianSign_measurable hBF).mono (F.mono h1a) le_rfl) 1
    (fun ω ↦ by rw [abs_brownianSign])
  have hK : K.toProcess = signedWindow B a b := by
    dsimp [K]
    rw [ElementaryIntegrand.toProcess_single]
    rfl
  rw [← hK]
  exact elementary_energy_ne_top K t

/-- The two adjacent signed windows differ by an elementary integrand of finite energy. -/
theorem signedDifference_energy_ne_top [IsFiniteMeasure P] (hBF : Adapted F B) (t : ℝ≥0) :
    ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t,
      ‖(signedWindow B 1 2 - signedWindow B 2 3) u.toNNReal ω‖ₑ ^ 2) ∂P ≠ ∞ := by
  rw [← signedDifference_toProcess hBF]
  exact elementary_energy_ne_top (signedDifference F B hBF) t

/-- The squared difference of the adjacent signed windows is `1` exactly on `(1, 3]`. -/
theorem signed_windows_sq (u : ℝ) (ω : Ω) :
    ‖signedWindow B 1 2 u.toNNReal ω - signedWindow B 2 3 u.toNNReal ω‖ₑ ^ 2 =
      (Set.Ioc (1 : ℝ) 3).indicator (fun _ ↦ (1 : ℝ≥0∞)) u := by
  rw [signedWindow, signedWindow, indicator_toNNReal, indicator_toNNReal]
  have hc : ‖brownianSign B ω‖ₑ ^ 2 = 1 := by
    rw [Real.enorm_eq_ofReal_abs, abs_brownianSign]
    norm_num
  by_cases h12 : u ∈ Set.Ioc (1 : ℝ) 2
  · have h23 : u ∉ Set.Ioc (2 : ℝ) 3 := by grind
    have h13 : u ∈ Set.Ioc (1 : ℝ) 3 := by grind
    simp [h12, h23, h13, hc]
  · by_cases h23 : u ∈ Set.Ioc (2 : ℝ) 3
    · have h13 : u ∈ Set.Ioc (1 : ℝ) 3 := by grind
      simp [h12, h23, h13, hc]
    · have h13 : u ∉ Set.Ioc (1 : ℝ) 3 := by grind
      simp [h12, h23, h13]

end MathlibExtTest.Probability.ItoIntegralSampleDependent
