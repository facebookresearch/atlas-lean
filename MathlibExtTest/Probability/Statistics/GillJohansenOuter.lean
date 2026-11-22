/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GillJohansenOuter
public import MathlibExtTest.Probability.Statistics.ContinuousProductIntegral

/-!
# Tests for the outer-probability Gill–Johansen framework

All non-vacuity facts below are computed from the definitions (`outerLIntegral`,
`TendstoInDistributionOuter`), not through the theorems under test.

* On the two-point space `Coin` with the trivial σ-algebra `⊥` and the Dirac measure at
  `⟨true⟩`, the outer integral of `𝟙{⟨false⟩}` is `1` while Mathlib's (lower) `lintegral` is `0`:
  the outer integral is a genuinely different functional on non-measurable functions.
* A sequence of non-measurable real processes on `Coin` that converges weakly in the outer sense
  to `δ₀`, although no Borel `TendstoInDistribution` statement about it can hold (each process
  fails to be a.e. measurable). So the outer framework is strictly more general.
* Usage: the outer functional delta theorem applied to that non-measurable sequence.
* Instances of both headline theorems, the Gill–Johansen limit
  `IsDuhamelProductIntegral.tendstoInDistributionOuter` and the Kaplan–Meier limit
  `tendstoInDistributionOuter_kmSurvival_lInfty`, on T78's degenerate witness
  `isStieltjesProductIntegral_zero` (horizon `τ = 0`) with constant processes. These show the
  hypothesis bundles are jointly satisfiable; they are not a genuine `τ > 0` instance.
-/

@[expose] public section

open MeasureTheory Filter Topology
open MathlibExt.Probability.Statistics.FunctionalDelta
open MathlibExt.Probability.Statistics.GillJohansenOuter
open MathlibExt.Probability.Statistics.ContinuousProductIntegral
open MathlibExtTest.Probability.Statistics.ContinuousProductIntegral
open MathlibExt.Probability.Statistics.KaplanMeier
open scoped ENNReal NNReal BoundedContinuousFunction

namespace MathlibExtTest.Probability.Statistics.GillJohansenOuter

/-- A two-point space. -/
structure Coin where
  /-- The underlying Boolean. -/
  b : Bool

/-- The trivial σ-algebra: only `∅` and `univ` are measurable. -/
instance : MeasurableSpace Coin := ⊥

/-- The Dirac measure at `⟨true⟩` on the trivial σ-algebra. -/
noncomputable def μc : Measure Coin := Measure.dirac ⟨true⟩

instance : IsProbabilityMeasure μc := by
  unfold μc
  infer_instance

/-- Measurable maps out of `Coin` into a space with measurable singletons are constant. -/
theorem measurable_coin_const {β : Type*} [MeasurableSpace β] [MeasurableSingletonClass β]
    {g : Coin → β} (hg : Measurable g) : g ⟨false⟩ = g ⟨true⟩ := by
  have hs := hg (measurableSet_singleton (g ⟨true⟩))
  rcases MeasurableSpace.measurableSet_bot_iff.1 hs with h | h
  · have : (⟨true⟩ : Coin) ∈ g ⁻¹' {g ⟨true⟩} := rfl
    rw [h] at this
    exact this.elim
  · have : (⟨false⟩ : Coin) ∈ g ⁻¹' {g ⟨true⟩} := by rw [h]; trivial
    exact this

/-- Every `μc`-null set is empty. -/
theorem eq_empty_of_null {s : Set Coin} (hs : μc s = 0) : s = ∅ := by
  obtain ⟨t, hst, htm, ht⟩ := exists_measurable_superset_of_null hs
  rcases MeasurableSpace.measurableSet_bot_iff.1 htm with h | h
  · exact Set.subset_eq_empty hst h
  · rw [h, measure_univ] at ht
    exact absurd ht one_ne_zero

/-- `μc`-almost-everywhere statements hold everywhere. -/
theorem forall_of_ae {p : Coin → Prop} (h : ∀ᵐ ω ∂μc, p ω) (ω : Coin) : p ω := by
  have h0 : μc {ω | ¬ p ω} = 0 := h
  have := eq_empty_of_null h0
  by_contra hω
  have hmem : ω ∈ {ω | ¬ p ω} := hω
  rw [this] at hmem
  exact hmem

/-- The indicator of `⟨false⟩`. -/
def indFalse (ω : Coin) : ℝ≥0∞ := if ω.b then 0 else 1

/-- The outer integral of `𝟙{⟨false⟩}` is `1`. -/
theorem outerLIntegral_indFalse : outerLIntegral μc indFalse = 1 := by
  refine le_antisymm ?_ ?_
  · refine (outerLIntegral_le_lintegral (g := fun _ ↦ 1) measurable_const
      (Eventually.of_forall fun ω ↦ ?_)).trans_eq (by simp)
    unfold indFalse
    split_ifs <;> simp
  · refine le_iInf fun g ↦ le_iInf fun hg ↦ le_iInf fun hfg ↦ ?_
    have h1 : (1 : ℝ≥0∞) ≤ g ⟨false⟩ := by simpa [indFalse] using forall_of_ae hfg ⟨false⟩
    rw [μc, lintegral_dirac' _ hg, ← measurable_coin_const hg]
    exact h1

/-- Mathlib's (lower) `lintegral` of `𝟙{⟨false⟩}` is `0`: every measurable minorant is a
constant bounded by its value `0` at `⟨true⟩`. -/
theorem lintegral_indFalse : ∫⁻ ω, indFalse ω ∂μc = 0 := by
  rw [← iSup_lintegral_measurable_le_eq_lintegral]
  refine le_antisymm (iSup_le fun g ↦ iSup_le fun hg ↦ iSup_le fun hgf ↦ ?_) (zero_le)
  have h0 : g ⟨true⟩ ≤ 0 := by simpa [indFalse] using hgf ⟨true⟩
  rw [μc, lintegral_dirac' _ hg]
  exact h0

/-- The outer integral strictly exceeds the lower integral on a non-measurable function. -/
example : ∫⁻ ω, indFalse ω ∂μc < outerLIntegral μc indFalse := by
  rw [lintegral_indFalse, outerLIntegral_indFalse]
  exact zero_lt_one

/-- A process on `Coin`: `0` at `⟨true⟩` and `x` at `⟨false⟩`. -/
def proc (x : ℝ) (ω : Coin) : ℝ := if ω.b then 0 else x

/-- `proc x` is not a.e. measurable for `x ≠ 0`. -/
theorem not_aemeasurable_proc {x : ℝ} (hx : x ≠ 0) : ¬ AEMeasurable (proc x) μc := by
  intro h
  have he := forall_of_ae h.ae_eq_mk
  have hc := measurable_coin_const h.measurable_mk
  have h1 : proc x ⟨false⟩ = proc x ⟨true⟩ := by rw [he, he, hc]
  simp [proc] at h1
  exact hx h1

/-- **Outer convergence of non-measurable processes**, from the definition: if `x n → 0` then
`proc (x n) ⇝ δ₀` in the outer sense. The outer integral of `f ∘ proc (x n)` lies between
`min (f 0) (f (x n))` and `max (f 0) (f (x n))`. -/
theorem tendstoInDistributionOuter_proc {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) :
    TendstoInDistributionOuter (fun n ↦ proc (x n)) μc ⟨Measure.dirac 0, inferInstance⟩ := by
  intro f
  simp only [ProbabilityMeasure.coe_mk]
  rw [lintegral_dirac]
  have hfx : Tendsto (fun n ↦ (f (x n) : ℝ≥0∞)) atTop (𝓝 (f 0 : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto _).comp ((f.continuous.tendsto 0).comp hx)
  have hmin : Tendsto (fun n ↦ min (f 0 : ℝ≥0∞) (f (x n))) atTop (𝓝 (f 0 : ℝ≥0∞)) := by
    simpa only [min_self] using (tendsto_const_nhds (x := ((f 0 : ℝ≥0) : ℝ≥0∞))).min hfx
  have hmax : Tendsto (fun n ↦ max (f 0 : ℝ≥0∞) (f (x n))) atTop (𝓝 (f 0 : ℝ≥0∞)) := by
    simpa only [max_self] using (tendsto_const_nhds (x := ((f 0 : ℝ≥0) : ℝ≥0∞))).max hfx
  have hval : ∀ n ω, (f (proc (x n) ω) : ℝ≥0∞) = if ω.b then (f 0 : ℝ≥0∞) else f (x n) := by
    intro n ω
    unfold proc
    split_ifs <;> rfl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hmin hmax (fun n ↦ ?_) (fun n ↦ ?_)
  · refine le_trans ?_ (lintegral_le_outerLIntegral _)
    calc min (f 0 : ℝ≥0∞) (f (x n)) = ∫⁻ _, min (f 0 : ℝ≥0∞) (f (x n)) ∂μc := by simp
      _ ≤ _ := lintegral_mono fun ω ↦ by
          rw [hval]
          split_ifs
          · exact min_le_left _ _
          · exact min_le_right _ _
  · refine (outerLIntegral_le_lintegral (g := fun _ ↦ max (f 0 : ℝ≥0∞) (f (x n)))
      measurable_const (Eventually.of_forall fun ω ↦ ?_)).trans_eq (by simp)
    simp only
    rw [hval]
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- The sequence `proc (1 / (n + 1))` converges weakly to `δ₀` in the outer sense... -/
example : TendstoInDistributionOuter (fun n : ℕ ↦ proc (1 / ((n : ℝ) + 1))) μc
    ⟨Measure.dirac 0, inferInstance⟩ :=
  tendstoInDistributionOuter_proc tendsto_one_div_add_atTop_nhds_zero_nat

/-- ... but no Borel convergence-in-distribution statement about it holds: already the first
process is not a.e. measurable. -/
example {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    (G : Ω' → ℝ) :
    ¬ TendstoInDistribution (fun n : ℕ ↦ proc (1 / ((n : ℝ) + 1))) atTop G (fun _ ↦ μc) μ' := by
  intro h
  exact not_aemeasurable_proc (by norm_num) (h.forall_aemeasurable 0)

/-- Usage of the outer functional delta theorem on non-measurable processes: with
`Xₙ = proc (1 / (n + 1))`, `r n = √(n + 1)` (so `r n • Xₙ = proc (1 / √(n + 1))`) and
`φ x = x ^ 2` (Fréchet derivative `0` at `0`), `r n • (Xₙ ^ 2 - 0) ⇝ δ₀ ∘ 0⁻¹`. -/
example : TendstoInDistributionOuter
    (fun (n : ℕ) ω ↦ √((n : ℝ) + 1) • (proc (1 / ((n : ℝ) + 1)) ω ^ 2 - (0 : ℝ) ^ 2)) μc
    (ProbabilityMeasure.map ⟨Measure.dirac 0, inferInstance⟩ fun _ : ℝ ↦ (0 : ℝ)) := by
  have hr : Tendsto (fun n : ℕ ↦ √((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hrX : (fun (n : ℕ) ω ↦ √((n : ℝ) + 1) • (proc (1 / ((n : ℝ) + 1)) ω - 0)) =
      fun (n : ℕ) ↦ proc (1 / √((n : ℝ) + 1)) := by
    funext n ω
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    unfold proc
    split_ifs
    · simp
    · rw [smul_eq_mul, sub_zero, one_div, one_div]
      field_simp
      rw [Real.sq_sqrt hpos.le]
  have hconv : TendstoInDistributionOuter
      (fun (n : ℕ) ω ↦ √((n : ℝ) + 1) • (proc (1 / ((n : ℝ) + 1)) ω - 0)) μc
      ⟨Measure.dirac 0, inferInstance⟩ := by
    rw [hrX]
    refine tendstoInDistributionOuter_proc ?_
    exact (tendsto_inv_atTop_zero.comp hr).congr fun n ↦ by simp [one_div]
  have hφ : HasHadamardDerivWithinAt (fun x : ℝ ↦ x ^ 2) (0 : ℝ →L[ℝ] ℝ) Set.univ Set.univ 0 := by
    refine HasFDerivAt.hasHadamardDerivWithinAt ?_ _ _
    simpa using (hasStrictFDerivAt_pow 2 (x := (0 : ℝ))).hasFDerivAt
  exact TendstoInDistributionOuter.functional_delta (φ := fun x : ℝ ↦ x ^ 2)
    (φ' := fun _ ↦ (0 : ℝ)) hconv hr hφ (by simp) (by simp) aemeasurable_const

/-! ### The headline theorems on T78's degenerate witness -/

/-- A constant process converges in the outer sense to the Dirac law at its value (from the
definition: the outer integral of a constant is the constant). -/
theorem tendstoInDistributionOuter_const {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : ℕ → Ω → E} {x : E} (hX : ∀ n ω, X n ω = x) :
    TendstoInDistributionOuter X μ ⟨Measure.dirac x, inferInstance⟩ := by
  intro f
  have hfm : Measurable fun y : E ↦ (f y : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp f.continuous.measurable
  simp only [ProbabilityMeasure.coe_mk, hX]
  rw [lintegral_dirac' _ hfm, outerLIntegral_eq_lintegral aemeasurable_const]
  simp

/-- **Gill–Johansen limit, instantiated** on `isStieltjesProductIntegral_zero` with the constant
integrator process `Aₙ = 0`, `θ = 0`, `r n = n`: the limit is the law of `Ψ 0 0 Z = 0`. -/
example :
    letI : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := borel _
    haveI : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := ⟨rfl⟩
    TendstoInDistributionOuter (fun (n : ℕ) (_ : Unit) ↦ (n : ℝ) • (one₀ - one₀))
      (Measure.dirac ())
      (ProbabilityMeasure.map ⟨Measure.dirac 0, inferInstance⟩
        ⇑(0 : lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞ →L[ℝ] _)) := by
  let _ : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := borel _
  have _ : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := ⟨rfl⟩
  exact IsDuhamelProductIntegral.tendstoInDistributionOuter
    isStieltjesProductIntegral_zero.toIsDuhamelProductIntegral (A := fun _ _ ↦ 0) (θ := 0)
    (r := fun n : ℕ ↦ (n : ℝ)) (Set.mem_univ _)
    (tendstoInDistributionOuter_const fun _ _ ↦ by simp) tendsto_natCast_atTop_atTop
    (by simp) (ae_of_all _ fun _ ↦ by simp)

/-- **Kaplan–Meier limit with outer probability, instantiated**: horizon `τ = 0`, constant data
`D₁` (no event in `[0, 0]`), so `Λ̂ = 0`, `Ŝ = 1`, and the limit is the law of `0`. -/
example :
    letI : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := borel _
    haveI : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := ⟨rfl⟩
    TendstoInDistributionOuter (fun (n : ℕ) (_ : Unit) ↦ √(n : ℝ) • (one₀ - one₀))
      (Measure.dirac ())
      (ProbabilityMeasure.map ⟨Measure.dirac 0, inferInstance⟩
        fun h ↦ -(0 : lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞ →L[ℝ] _) h) := by
  let _ : MeasurableSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := borel _
  have _ : BorelSpace (lp (fun _ : Set.Icc (0 : ℝ) 0 ↦ ℝ) ∞) := ⟨rfl⟩
  refine tendstoInDistributionOuter_kmSurvival_lInfty isStieltjesProductIntegral_zero
    (Dn := fun _ _ ↦ D₁) (fun _ _ _ ↦ one_pos) (Λhat := fun _ _ ↦ 0) (KMhat := fun _ _ ↦ one₀)
    (Λ := 0) ?_ ?_ (Set.mem_univ _) (tendstoInDistributionOuter_const fun _ _ ↦ by simp)
    (ae_of_all _ fun _ ↦ by simp) (by simp)
  · intro _ _ t
    rw [CensoredData.nelsonAalen, filter_eq_empty_of_pos D₁.time (fun _ ↦ one_pos) t,
      Finset.sum_empty]
    rfl
  · intro _ _ t
    rw [CensoredData.kmSurvival, filter_eq_empty_of_pos D₁.time (fun _ ↦ one_pos) t,
      Finset.prod_empty]
    rfl

end MathlibExtTest.Probability.Statistics.GillJohansenOuter
