/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Continuous-time counting processes, risk processes and their compensators

The continuous-time counting-process model of survival analysis under random right censoring,
built from latent times, with its compensator identities proved rather than assumed.

## The model

One subject has a latent failure time `T : Ω → ℝ` and a censoring time `C : Ω → ℝ` on a
probability space `(Ω, P)`. One observes `X = T ∧ C` (`obsTime`) and `δ = 1{T ≤ C}` (ties count as
failures). From these:

* `countingProcess`: `N(t) = 1{X ≤ t, δ = 1}`, the observed-failure counting process;
* `censoringProcess`: `Nᶜ(t) = 1{X ≤ t, δ = 0}`;
* `atRiskProcess`: `Y(t) = 1{t ≤ X}`, the left-continuous at-risk indicator;
* `hazardMeasure F`: the hazard measure `dΛ(s) = dF(s) / F[s, ∞)` of the law `F` of `T`,
  for any law with or without atoms (`hazardMeasure_withDensity`: `dΛ = λ(s) ds` with `λ = f / S₋`
  when `F` has density `f`);
* `compensator`: `A(t) = ∫_{(-∞, t]} Y dΛ = Λ((-∞, t ∧ X])` (`compensator_eq`);
* `compensatedProcess`: `M(t) = N(t) - A(t)`;
* `historyFiltration`: `ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)`, the natural filtration of the observed
  process `(N, Nᶜ)` (`observedProcess`).

**Hypotheses.** `T`, `C` measurable, and **independent censoring** `T ⊥ C` (`IndepFun T C P`).
No density, continuity or support condition is put on either law. For `n` subjects
(`jointHistoryFiltration`, `totalCountingProcess`, `totalAtRiskProcess`, `totalCompensator`), the
pairs `(Tᵢ, Cᵢ)` are mutually independent (`iIndepFun`) and `Tᵢ ⊥ Cᵢ` for each `i`; the laws may
differ between subjects.

## Main results (compensator identities)

* `lintegral_hazardMeasure_inter_Iic_obsTime`: `E[Λ(B ∩ (-∞, X])] = P(T ∈ B, T ≤ C)` for every
  Borel `B`, i.e. `E ∫_B Y dΛ = E ∫_B dN`.
* `integral_countingProcess_eq_integral_compensator`: `E N(t) = E A(t)`.
* `martingale_compensatedProcess`: `N - A` is a martingale for the history filtration.
* `measurable_atRiskProcess_strictPast`, `measurable_compensator_strictPast`: `Y(t)` and `A(t)`
  are determined by the strict past `ℱ_{t-} = ⨆_{s < t} ℱₛ`. So `A` is a compensator of `N` in
  the sense that `N - A` is a martingale and `A(t)` is `ℱ_{t-}`-measurable (intensity
  `Y(t) dΛ(t)`); uniqueness of the compensator is not proved.
* `martingale_compensatedProcess_joint`: in a cohort, each subject's `Nᵢ - Aᵢ` is a martingale for
  the joint history of all subjects.
* `martingale_totalCountingProcess_sub_totalCompensator`: `∑ᵢ Nᵢ - ∑ᵢ Aᵢ` is a martingale for the
  joint history. When all `Tᵢ` share one law `F`, `totalCompensator_eq_of_map_eq` gives
  `∑ᵢ Aᵢ(t) = ∫_{(-∞, t]} Y dΛ` with `Y` the number at risk and `Λ` the hazard measure of `F`
  (Aalen's multiplicative intensity model).

The key step is `history_inter_or_subset`: an event observed by time `a` either contains
`{X > a}` or is disjoint from it, so the conditional identity reduces to the unconditional one.

## Boundary cases

* **Atoms.** An atom of `F` at `s` gives `Λ` the atom `F{s} / F[s, ∞)`, which is `1` at a terminal
  atom; the martingale statement covers this case.
* **Vanishing tail.** Where `F[s, ∞) = 0` the hazard density is `0⁻¹ = ∞`. That set has
  `F`-measure zero (`ae_measure_Ici_ne_zero`), and the extended compensator `Λ((-∞, t ∧ X])` has
  finite mean (`lintegral_hazardMeasure_Iic_obsTime_lt_top`). `compensator` takes `ENNReal.toReal`
  of it, which affects only a null set.
* **Ties** `T = C` are counted as observed failures.

## Scope

* The predictable σ-algebra on `ℝ × Ω`, Doob–Meyer decomposition and uniqueness of compensators
  are not built. Predictability is stated as `ℱ_{t-}`-measurability, and `A` is shown to be a
  compensator by exhibiting the martingale `N - A`.
* Left truncation, dependent censoring, covariate (Cox) intensities, predictable variation in
  continuous time and the martingale central limit theorem are not treated here. Limit theorems
  and inference built on these identities belong to downstream modules.
* The discrete-grid calculus (stochastic integrals, Nelson–Aalen and Kaplan–Meier martingales on
  `ℕ`) is `MathlibExt/Probability/Statistics/Survival/StochasticIntegral.lean`, which this file
  does not import or duplicate.

## Reused API (source receipts)

* `MeasureTheory.Martingale`, `MeasureTheory.Filtration.natural`, `StronglyAdapted`
  (`Mathlib/Probability/Martingale/Basic.lean`, `Mathlib/Probability/Process/Filtration.lean`).
* `MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq`, `MeasureTheory.condExp_indep_eq`
  (`Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`,
  `Mathlib/Probability/ConditionalExpectation.lean`).
* `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`, `indep_iSup_of_disjoint`,
  `iIndepFun_iff_iIndep` (`Mathlib/Probability/Independence/Basic.lean`).
* `MeasureTheory.Measure.withDensity`, `Measure.prod_apply`, `Measure.prod_apply_symm`,
  `MeasurableSet.measure_eq_iSup_isCompact_of_ne_top`, `MeasurableSpace.induction_on_inter`.

## References

* O. O. Aalen, *Nonparametric inference for a family of counting processes*, Ann. Statist. 6
  (1978), 701–726.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Sections II.4 (counting processes, compensators, multiplicative
  intensity) and III.2 (independent right censoring).
* T. R. Fleming and D. P. Harrington, *Counting Processes and Survival Analysis*, Wiley (1991),
  Section 1.3 (the compensator of a single-jump counting process under random censorship).
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-! ### The censoring model and its processes -/

/-- The **observed time** `X = T ∧ C` of a subject with latent failure time `T` and censoring
time `C`. -/
def obsTime (T C : Ω → ℝ) (ω : Ω) : ℝ := min (T ω) (C ω)

/-- The **counting process** `N(t) = 1{X ≤ t, δ = 1} = 1{T ≤ C, T ≤ t}` of observed failures.
Ties `T = C` count as observed failures (failure precedes censoring). -/
noncomputable def countingProcess (T C : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if T ω ≤ C ω ∧ T ω ≤ t then 1 else 0

/-- The **censoring counting process** `Nᶜ(t) = 1{X ≤ t, δ = 0} = 1{C < T, C ≤ t}`. Together with
`countingProcess` it generates the observed history (`historyFiltration`). -/
noncomputable def censoringProcess (T C : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if C ω < T ω ∧ C ω ≤ t then 1 else 0

/-- The **at-risk process** `Y(t) = 1{t ≤ X} = 1{t ≤ T, t ≤ C}`: the subject is under observation
just before `t`. It is left-continuous, so `Y(t)` is `ℱ_{t-}`-measurable
(`measurable_atRiskProcess_strictPast`). -/
noncomputable def atRiskProcess (T C : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if t ≤ T ω ∧ t ≤ C ω then 1 else 0

/-- The **hazard measure** `dΛ(s) = dF(s) / F[s, ∞)` of a law `F` on `ℝ`, i.e. the cumulative
hazard `Λ(t) = ∫_{(-∞, t]} dF(s) / F([s, ∞))` as a measure. For a law with a density `f` it is
`λ(s) ds` with hazard rate `λ = f / S(s-)` (`hazardMeasure_withDensity`); an atom of `F` at `s`
gives `Λ` the atom `F{s} / F[s, ∞) ≤ 1`. Convention `0⁻¹ = ∞`: the density is infinite where
`F[s, ∞) = 0`, a set of `F`-measure zero (`ae_measure_Ici_ne_zero`). -/
noncomputable def hazardMeasure (F : Measure ℝ) : Measure ℝ :=
  F.withDensity fun s => (F (Ici s))⁻¹

/-- The **compensator** `A(t) = ∫_{(-∞, t]} Y(s) dΛ(s)` of the counting process for a hazard
measure `Λ`, as a real number (`ENNReal.toReal`; the extended value is finite almost surely
under the model, `lintegral_hazardMeasure_Iic_obsTime_lt_top`). -/
noncomputable def compensator (T C : Ω → ℝ) (Λ : Measure ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  (∫⁻ s in Iic t, ENNReal.ofReal (atRiskProcess T C s ω) ∂Λ).toReal

variable {T C : Ω → ℝ}

/-- `N(t) = 1` exactly when a failure has been observed by time `t`. -/
theorem countingProcess_eq_one_iff {t : ℝ} {ω : Ω} :
    countingProcess T C t ω = 1 ↔ T ω ≤ C ω ∧ T ω ≤ t := by
  unfold countingProcess; split_ifs with h <;> simp [h]

/-- The counting process of one subject takes values in `{0, 1}`. -/
theorem countingProcess_mem (t : ℝ) (ω : Ω) : countingProcess T C t ω ∈ ({0, 1} : Set ℝ) := by
  unfold countingProcess; split_ifs <;> simp

/-- The at-risk process takes values in `{0, 1}`. -/
theorem atRiskProcess_mem (t : ℝ) (ω : Ω) : atRiskProcess T C t ω ∈ ({0, 1} : Set ℝ) := by
  unfold atRiskProcess; split_ifs <;> simp

/-- The at-risk indicator is `1{t ≤ X}`. -/
theorem atRiskProcess_eq_indicator (t : ℝ) (ω : Ω) :
    atRiskProcess T C t ω = (Iic (obsTime T C ω)).indicator 1 t := by
  simp [atRiskProcess, obsTime, indicator]

/-- The counting process has non-decreasing paths. -/
theorem countingProcess_mono (ω : Ω) : Monotone fun t => countingProcess T C t ω := by
  intro s t hst
  simp only [countingProcess]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h1.2.trans hst⟩ h2
  · exact zero_le_one
  · exact le_rfl

/-- The at-risk process has non-increasing paths. -/
theorem atRiskProcess_anti (ω : Ω) : Antitone fun t => atRiskProcess T C t ω := by
  intro s t hst
  simp only [atRiskProcess]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨hst.trans h1.1, hst.trans h1.2⟩ h2
  · exact zero_le_one
  · exact le_rfl

/-- The counting process starts at `0` before the observed time: `N(t) = 0` for `t < X`. -/
theorem countingProcess_of_lt_obsTime {t : ℝ} {ω : Ω} (h : t < obsTime T C ω) :
    countingProcess T C t ω = 0 := by
  simp only [obsTime, lt_min_iff] at h
  simp [countingProcess, not_le.2 h.1]

/-- The censoring process vanishes before the observed time. -/
theorem censoringProcess_of_lt_obsTime {t : ℝ} {ω : Ω} (h : t < obsTime T C ω) :
    censoringProcess T C t ω = 0 := by
  simp only [obsTime, lt_min_iff] at h
  simp [censoringProcess, not_le.2 h.2]

/-- Each subject exits exactly once: `N(t) + Nᶜ(t) = 1{X ≤ t}`. -/
theorem countingProcess_add_censoringProcess (t : ℝ) (ω : Ω) :
    countingProcess T C t ω + censoringProcess T C t ω =
      if obsTime T C ω ≤ t then 1 else 0 := by
  simp only [countingProcess, censoringProcess, obsTime, min_le_iff]
  by_cases h : T ω ≤ C ω
  · have : ¬ C ω < T ω := not_lt.2 h
    by_cases ht : T ω ≤ t
    · simp [h, ht, this]
    · simp [h, ht, this, show ¬ C ω ≤ t from fun hc => ht (h.trans hc)]
  · have h' : C ω < T ω := not_le.1 h
    by_cases hc : C ω ≤ t
    · simp [h, h', hc]
    · simp [h, h', hc, show ¬ T ω ≤ t from fun ht => hc (h'.le.trans ht)]

/-- The counting process is frozen after the observed time: `N(t) = N(X)` for `X ≤ t`. -/
theorem countingProcess_of_obsTime_le {t : ℝ} {ω : Ω} (h : obsTime T C ω ≤ t) :
    countingProcess T C t ω = countingProcess T C (obsTime T C ω) ω := by
  simp only [countingProcess, obsTime] at h ⊢
  by_cases hTC : T ω ≤ C ω
  · rw [min_eq_left hTC] at h
    simp [hTC, h]
  · simp [hTC]

/-- The compensator is `Λ((-∞, t ∧ X])`. -/
theorem compensator_eq (Λ : Measure ℝ) (t : ℝ) (ω : Ω) :
    compensator T C Λ t ω = (Λ (Iic (min t (obsTime T C ω)))).toReal := by
  simp only [compensator, atRiskProcess_eq_indicator]
  rw [← Iic_inter_Iic, ← lintegral_indicator_one (measurableSet_Iic.inter measurableSet_Iic),
    ← lintegral_indicator measurableSet_Iic]
  congr 2
  funext s
  by_cases h1 : s ≤ t <;> by_cases h2 : s ≤ obsTime T C ω <;>
    simp [h1, h2, indicator, Set.mem_Iic]

/-! ### The hazard measure -/

/-- The survival-type function `s ↦ F[s, ∞)` is measurable (it is antitone). -/
theorem measurable_measure_Ici (F : Measure ℝ) : Measurable fun s => F (Ici s) :=
  Antitone.measurable fun _ _ h => measure_mono (Ici_subset_Ici.2 h)

/-- For a finite law `F` on `ℝ`, almost every point `s` has positive right tail mass
`F[s, ∞) ≠ 0`: the set where the tail vanishes is an upper set, and every compact subset of it
lies in `[min K, ∞)`, which has measure zero. -/
theorem ae_measure_Ici_ne_zero (F : Measure ℝ) [IsFiniteMeasure F] :
    ∀ᵐ s ∂F, F (Ici s) ≠ 0 := by
  set S : Set ℝ := {s | F (Ici s) = 0} with hS
  have hup : IsUpperSet S := fun a b hab ha =>
    le_antisymm ((measure_mono (Ici_subset_Ici.2 hab)).trans_eq ha) bot_le
  have hmeas : MeasurableSet S := hup.ordConnected.measurableSet
  change F {s | ¬ F (Ici s) ≠ 0} = 0
  simp only [not_not]
  rw [hmeas.measure_eq_iSup_isCompact_of_ne_top (measure_ne_top F S)]
  refine ENNReal.iSup_eq_zero.2 fun K => ENNReal.iSup_eq_zero.2 fun hKS =>
    ENNReal.iSup_eq_zero.2 fun hK => ?_
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact measure_empty
  · refine le_antisymm ((measure_mono fun x hx => ?_).trans_eq (hKS (hK.sInf_mem hne))) bot_le
    exact (hK.bddBelow.mono le_rfl |> fun hb => csInf_le hb hx)

/-- The hazard measure of a law with density `f` has density `λ(s) = f(s) / F[s, ∞)`, the
**hazard rate**: `dΛ = λ(s) ds`. -/
theorem hazardMeasure_withDensity {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    hazardMeasure (volume.withDensity f) =
      volume.withDensity fun s => f s * ((volume.withDensity f) (Ici s))⁻¹ := by
  rw [hazardMeasure, ← withDensity_mul _ hf
    (g := fun s => ((volume.withDensity f) (Ici s))⁻¹) (measurable_measure_Ici _).inv]
  rfl

/-! ### The compensator identity in mean -/

variable {μ : Measure Ω}

private lemma measurable_hazard_inter_Iic (Λ : Measure ℝ) (B : Set ℝ) :
    Measurable fun x : ℝ => Λ (B ∩ Iic x) :=
  Monotone.measurable fun _ _ h => measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 h))

/-- **Compensator identity in mean** for the random-censorship model. Let the latent failure
time `T` and censoring time `C` be independent, `F` the law of `T` and `Λ` its hazard measure.
For every Borel set `B` of times,
`E[Λ(B ∩ (-∞, X])] = E[∫_B Y dΛ] = P(T ∈ B, T ≤ C) = E[∫_B dN]`:
the expected compensator mass of `B` equals the expected number of observed failures in `B`.
Independent censoring is used through `P(T ≥ s, C ≥ s) = F[s, ∞) G[s, ∞)`. -/
theorem lintegral_hazardMeasure_inter_Iic_obsTime [IsProbabilityMeasure μ] (hT : Measurable T)
    (hC : Measurable C) (hind : IndepFun T C μ) {B : Set ℝ} (hB : MeasurableSet B) :
    ∫⁻ ω, hazardMeasure (μ.map T) (B ∩ Iic (obsTime T C ω)) ∂μ =
      μ {ω | T ω ∈ B ∧ T ω ≤ C ω} := by
  set F := μ.map T with hF
  set G := μ.map C with hG
  set Λ := hazardMeasure F with hΛ
  have : SFinite Λ := by rw [hΛ, hazardMeasure]; infer_instance
  have hTC : Measurable fun ω => (T ω, C ω) := hT.prodMk hC
  have hprod : μ.map (fun ω => (T ω, C ω)) = F.prod G :=
    (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hC.aemeasurable).1 hind
  -- the event set `E = {((x, y), s) | s ∈ B, s ≤ x, s ≤ y}`
  set E : Set ((ℝ × ℝ) × ℝ) := {q | q.2 ∈ B ∧ q.2 ≤ q.1.1 ∧ q.2 ≤ q.1.2} with hE
  have hEm : MeasurableSet E :=
    (measurable_snd hB).inter ((measurableSet_le measurable_snd measurable_fst.fst).inter
      (measurableSet_le measurable_snd measurable_fst.snd))
  -- left side as an integral over the product law
  have hL : ∫⁻ ω, Λ (B ∩ Iic (obsTime T C ω)) ∂μ = ((F.prod G).prod Λ) E := by
    have hmeas : Measurable fun p : ℝ × ℝ => Λ (B ∩ Iic (min p.1 p.2)) :=
      (measurable_hazard_inter_Iic Λ B).comp (measurable_fst.min measurable_snd)
    have hfun : (fun p : ℝ × ℝ => Λ (Prod.mk p ⁻¹' E)) =
        fun p => Λ (B ∩ Iic (min p.1 p.2)) := by
      funext p; congr 1; ext s; simp only [hE, mem_preimage, mem_ofPred_eq, mem_inter_iff, mem_Iic,
        le_min_iff]
    rw [Measure.prod_apply hEm, hfun, ← hprod, lintegral_map hmeas hTC]
    rfl
  -- swap the order and evaluate the inner product-measure of each slice
  have hslice : ∀ s, (F.prod G) ((fun p => (p, s)) ⁻¹' E) =
      B.indicator (fun s => F (Ici s) * G (Ici s)) s := by
    intro s
    by_cases hs : s ∈ B
    · have : (fun p => (p, s)) ⁻¹' E = Ici s ×ˢ Ici s := by
        ext p; simp [hE, hs, Prod.le_def]
      rw [this, Measure.prod_prod, indicator_of_mem hs]
    · have : (fun p => (p, s)) ⁻¹' E = ∅ := by
        ext p; simp [hE, hs]
      rw [this, measure_empty, indicator_of_notMem hs]
  have hmeasFG : Measurable fun s => F (Ici s) * G (Ici s) :=
    (measurable_measure_Ici F).mul (measurable_measure_Ici G)
  rw [hL, Measure.prod_apply_symm hEm]
  simp_rw [hslice]
  rw [lintegral_indicator hB, hΛ, hazardMeasure,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (f := fun s => (F (Ici s))⁻¹)
      (measurable_measure_Ici F).inv hmeasFG hB]
  -- cancel `F[s, ∞)⁻¹ * F[s, ∞)` almost everywhere
  have hcancel : ∫⁻ s in B, ((fun s => (F (Ici s))⁻¹) * fun s => F (Ici s) * G (Ici s)) s ∂F =
      ∫⁻ s in B, G (Ici s) ∂F := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [ae_measure_Ici_ne_zero F] with s hs
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hs (measure_ne_top F _), one_mul]
  rw [hcancel]
  -- right side through the product law
  have hR : μ {ω | T ω ∈ B ∧ T ω ≤ C ω} = (F.prod G) {p | p.1 ∈ B ∧ p.1 ≤ p.2} := by
    have hm : MeasurableSet {p : ℝ × ℝ | p.1 ∈ B ∧ p.1 ≤ p.2} :=
      (measurable_fst hB).inter (measurableSet_le measurable_fst measurable_snd)
    rw [← hprod, Measure.map_apply hTC hm]
    rfl
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 ∈ B ∧ p.1 ≤ p.2} :=
    (measurable_fst hB).inter (measurableSet_le measurable_fst measurable_snd)
  rw [hR, Measure.prod_apply hm, ← lintegral_indicator hB]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ B
  · rw [indicator_of_mem hx]
    congr 1; ext y; simp [hx]
  · rw [indicator_of_notMem hx]
    have : Prod.mk x ⁻¹' {p : ℝ × ℝ | p.1 ∈ B ∧ p.1 ≤ p.2} = ∅ := by ext y; simp [hx]
    rw [this, measure_empty]

/-! ### Measurability, integrability and the mean identity `E N(t) = E A(t)` -/

/-- The counting process is the indicator of the event `{T ≤ C, T ≤ t}`. -/
theorem countingProcess_eq_indicator (t : ℝ) :
    countingProcess T C t = {ω | T ω ≤ C ω ∧ T ω ≤ t}.indicator 1 := by
  funext ω
  by_cases h : T ω ≤ C ω ∧ T ω ≤ t <;> simp [countingProcess, h]

/-- The counting process is measurable at each time. -/
theorem measurable_countingProcess (hT : Measurable T) (hC : Measurable C) (t : ℝ) :
    Measurable (countingProcess T C t) := by
  rw [countingProcess_eq_indicator]
  exact measurable_one.indicator ((measurableSet_le hT hC).inter (measurableSet_le hT
    measurable_const))

/-- The censoring process is measurable at each time. -/
theorem measurable_censoringProcess (hT : Measurable T) (hC : Measurable C) (t : ℝ) :
    Measurable (censoringProcess T C t) :=
  Measurable.ite ((measurableSet_lt hC hT).inter (measurableSet_le hC measurable_const))
    measurable_const measurable_const

/-- The compensator is `Λ((-∞, t] ∩ (-∞, X])`. -/
theorem compensator_eq_toReal (Λ : Measure ℝ) (t : ℝ) (ω : Ω) :
    compensator T C Λ t ω = (Λ (Iic t ∩ Iic (obsTime T C ω))).toReal := by
  rw [compensator_eq, Iic_inter_Iic]

private lemma measurable_hazard_obsTime (Λ : Measure ℝ) (B : Set ℝ) (hT : Measurable T)
    (hC : Measurable C) : Measurable fun ω => Λ (B ∩ Iic (obsTime T C ω)) :=
  (measurable_hazard_inter_Iic Λ B).comp (hT.min hC)

/-- The extended compensator `Λ((-∞, t ∧ X])` has finite mean, hence is finite almost surely. -/
theorem lintegral_hazardMeasure_Iic_obsTime_lt_top [IsProbabilityMeasure μ] (hT : Measurable T)
    (hC : Measurable C) (hind : IndepFun T C μ) (t : ℝ) :
    ∫⁻ ω, hazardMeasure (μ.map T) (Iic t ∩ Iic (obsTime T C ω)) ∂μ < ∞ := by
  rw [lintegral_hazardMeasure_inter_Iic_obsTime hT hC hind measurableSet_Iic]
  exact measure_lt_top _ _

private lemma compensator_fun_eq (Λ : Measure ℝ) (t : ℝ) :
    compensator T C Λ t = fun ω => (Λ (Iic t ∩ Iic (obsTime T C ω))).toReal :=
  funext fun ω => compensator_eq_toReal Λ t ω

/-- The counting process is integrable (it is a bounded indicator). -/
theorem integrable_countingProcess [IsFiniteMeasure μ] (hT : Measurable T) (hC : Measurable C)
    (t : ℝ) : Integrable (countingProcess T C t) μ := by
  rw [countingProcess_eq_indicator]
  exact (integrable_const 1).indicator ((measurableSet_le hT hC).inter
    (measurableSet_le hT measurable_const))

/-- Under independent censoring the compensator is integrable (its mean is `P(T ≤ t, T ≤ C)`). -/
theorem integrable_compensator [IsProbabilityMeasure μ] (hT : Measurable T) (hC : Measurable C)
    (hind : IndepFun T C μ) (t : ℝ) :
    Integrable (compensator T C (hazardMeasure (μ.map T)) t) μ := by
  rw [compensator_fun_eq]
  exact integrable_toReal_of_lintegral_ne_top
    (measurable_hazard_obsTime _ _ hT hC).aemeasurable
    (lintegral_hazardMeasure_Iic_obsTime_lt_top hT hC hind t).ne

/-- **Compensator identity in mean**: `E[N(t)] = E[A(t)] = P(T ≤ t, T ≤ C)` for every `t`. -/
theorem integral_countingProcess_eq_integral_compensator [IsProbabilityMeasure μ]
    (hT : Measurable T) (hC : Measurable C) (hind : IndepFun T C μ) (t : ℝ) :
    ∫ ω, countingProcess T C t ω ∂μ =
      ∫ ω, compensator T C (hazardMeasure (μ.map T)) t ω ∂μ := by
  have hm := measurable_hazard_obsTime (hazardMeasure (μ.map T)) (Iic t) hT hC
  rw [compensator_fun_eq, integral_toReal hm.aemeasurable
    (ae_lt_top' hm.aemeasurable (lintegral_hazardMeasure_Iic_obsTime_lt_top hT hC hind t).ne),
    lintegral_hazardMeasure_inter_Iic_obsTime hT hC hind measurableSet_Iic,
    countingProcess_eq_indicator]
  have hs : MeasurableSet {ω | T ω ≤ C ω ∧ T ω ≤ t} :=
    (measurableSet_le hT hC).inter (measurableSet_le hT measurable_const)
  rw [integral_indicator hs]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one,
    Measure.real, mem_Iic, and_comm]

/-! ### The history filtration -/

/-- The **observed process** `(N(t), Nᶜ(t))`: what the statistician sees of one subject at time
`t` (whether the subject has failed, or has been censored, by time `t`). -/
noncomputable def observedProcess (T C : Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ × ℝ :=
  (countingProcess T C t ω, censoringProcess T C t ω)

/-- The observed process is strongly measurable at each time. -/
theorem stronglyMeasurable_observedProcess (hT : Measurable T) (hC : Measurable C) (t : ℝ) :
    StronglyMeasurable (observedProcess T C t) :=
  ((measurable_countingProcess hT hC t).prodMk
    (measurable_censoringProcess hT hC t)).stronglyMeasurable

/-- The **history filtration** `ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)`: the natural filtration of the
observed process (the "self-exciting" filtration of Andersen–Borgan–Gill–Keiding). -/
noncomputable def historyFiltration (hT : Measurable T) (hC : Measurable C) : Filtration ℝ m0 :=
  Filtration.natural (observedProcess T C) (stronglyMeasurable_observedProcess hT hC)

variable (hT : Measurable T) (hC : Measurable C)

/-- The observed process at time `u` is known at every later time `t ≥ u`. -/
theorem measurable_observedProcess_history {u t : ℝ} (hut : u ≤ t) :
    Measurable[historyFiltration hT hC t] (observedProcess T C u) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂ (f := fun j (_ : j ≤ t) =>
    MeasurableSpace.comap (observedProcess T C j) inferInstance) u hut

/-- The counting process is adapted to the history. -/
theorem measurable_countingProcess_history {u t : ℝ} (hut : u ≤ t) :
    Measurable[historyFiltration hT hC t] (countingProcess T C u) :=
  measurable_fst.comp (measurable_observedProcess_history hT hC hut)

/-- The event "exited by time `x`" is observed at every time `t ≥ x`. -/
theorem measurableSet_obsTime_le_history {x t : ℝ} (hxt : x ≤ t) :
    MeasurableSet[historyFiltration hT hC t] {ω | obsTime T C ω ≤ x} := by
  have : {ω | obsTime T C ω ≤ x} = observedProcess T C x ⁻¹' {p | p.1 + p.2 = 1} := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, observedProcess, countingProcess_add_censoringProcess]
    split_ifs with h <;> simp [h]
  rw [this]
  exact measurable_observedProcess_history hT hC hxt
    (measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const)

/-- The **strict past** `ℱ_{t-} = ⨆_{s < t} ℱₛ` determines the stopped exit time `t ∧ X`. -/
theorem measurable_min_obsTime_strictPast (t : ℝ) :
    Measurable[⨆ s < t, historyFiltration hT hC s] fun ω => min t (obsTime T C ω) := by
  refine measurable_of_Iic fun x => ?_
  by_cases hx : t ≤ x
  · have : (fun ω => min t (obsTime T C ω)) ⁻¹' Iic x = univ :=
      eq_univ_of_forall fun ω => (min_le_left _ _).trans hx
    rw [this]; exact MeasurableSet.univ
  · have : (fun ω => min t (obsTime T C ω)) ⁻¹' Iic x = {ω | obsTime T C ω ≤ x} := by
      ext ω; simp [min_le_iff, hx]
    rw [this]
    exact le_iSup₂ (f := fun s (_ : s < t) => historyFiltration hT hC s) x (not_le.1 hx) _
      (measurableSet_obsTime_le_history hT hC le_rfl)

/-- The at-risk process is **predictable** in the sense that `Y(t)` is determined by the strict
past `ℱ_{t-}` (it is left-continuous and adapted). -/
theorem measurable_atRiskProcess_strictPast (t : ℝ) :
    Measurable[⨆ s < t, historyFiltration hT hC s] (atRiskProcess T C t) := by
  have : atRiskProcess T C t = (fun y => if t ≤ y then (1 : ℝ) else 0) ∘
      fun ω => min t (obsTime T C ω) := by
    funext ω
    simp only [atRiskProcess, Function.comp, le_min_iff, le_refl, true_and, obsTime]
  rw [this]
  exact (Measurable.ite measurableSet_Ici measurable_const measurable_const).comp
    (measurable_min_obsTime_strictPast hT hC t)

/-- The compensator is **predictable** in the same sense: `A(t)` is determined by `ℱ_{t-}`. -/
theorem measurable_compensator_strictPast (Λ : Measure ℝ) (t : ℝ) :
    Measurable[⨆ s < t, historyFiltration hT hC s] (compensator T C Λ t) := by
  have : compensator T C Λ t = (fun y => (Λ (Iic y)).toReal) ∘
      fun ω => min t (obsTime T C ω) := funext fun ω => compensator_eq Λ t ω
  rw [this]
  exact (ENNReal.measurable_toReal.comp (Monotone.measurable fun _ _ h =>
    measure_mono (Iic_subset_Iic.2 h))).comp (measurable_min_obsTime_strictPast hT hC t)

/-- The strict past `ℱ_{t-}` is contained in `ℱₜ`. -/
theorem strictPast_le_history (t : ℝ) :
    (⨆ s < t, historyFiltration hT hC s) ≤ historyFiltration hT hC t :=
  iSup₂_le fun _ hs => (historyFiltration hT hC).mono hs.le

/-- The σ-algebra of sets that either contain `E` or miss it. -/
@[instance_reducible]
private def trivialOn (E : Set Ω) : MeasurableSpace Ω where
  MeasurableSet' A := A ∩ E = ∅ ∨ E ⊆ A
  measurableSet_empty := Or.inl (empty_inter E)
  measurableSet_compl A hA := by
    rcases hA with h | h
    · exact Or.inr fun x hx hxA => (h.subset ⟨hxA, hx⟩ : x ∈ (∅ : Set Ω))
    · exact Or.inl (eq_empty_of_forall_notMem fun x hx => hx.1 (h hx.2))
  measurableSet_iUnion f hf := by
    by_cases h : ∃ i, E ⊆ f i
    · obtain ⟨i, hi⟩ := h
      exact Or.inr (hi.trans (subset_iUnion f i))
    · push Not at h
      left
      rw [iUnion_inter]
      exact iUnion_eq_empty.2 fun i => (hf i).resolve_right (h i)

/-- **The history before exit is trivial**: every event observed by time `a` either contains the
event `{X > a}` "still under observation after `a`" or is disjoint from it. -/
theorem history_inter_or_subset {a : ℝ} {A : Set Ω}
    (hA : MeasurableSet[historyFiltration hT hC a] A) :
    A ∩ {ω | a < obsTime T C ω} = ∅ ∨ {ω | a < obsTime T C ω} ⊆ A := by
  suffices h : historyFiltration hT hC a ≤ trivialOn {ω | a < obsTime T C ω} from h A hA
  refine iSup₂_le fun u hu => ?_
  rintro _ ⟨B, -, rfl⟩
  have hE : ∀ ω, a < obsTime T C ω → observedProcess T C u ω = (0, 0) := fun ω hω => by
    simp [observedProcess, countingProcess_of_lt_obsTime (hu.trans_lt hω),
      censoringProcess_of_lt_obsTime (hu.trans_lt hω)]
  change observedProcess T C u ⁻¹' B ∩ _ = ∅ ∨ _ ⊆ observedProcess T C u ⁻¹' B
  by_cases h0 : ((0 : ℝ), (0 : ℝ)) ∈ B
  · exact Or.inr fun ω hω => by simp only [mem_preimage, hE ω hω, h0]
  · exact Or.inl (eq_empty_of_forall_notMem fun ω hω => h0 (by
      have := hω.1; rwa [mem_preimage, hE ω hω.2] at this))

/-! ### The compensated counting process is a martingale -/

/-- The **compensated counting process** `M(t) = N(t) - A(t) = N(t) - ∫_{(-∞, t]} Y dΛ`. -/
noncomputable def compensatedProcess (T C : Ω → ℝ) (Λ : Measure ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  countingProcess T C t ω - compensator T C Λ t ω

include hT hC in
/-- Under independent censoring the compensated process is integrable. -/
theorem integrable_compensatedProcess [IsProbabilityMeasure μ] (hind : IndepFun T C μ) (t : ℝ) :
    Integrable (compensatedProcess T C (hazardMeasure (μ.map T)) t) μ :=
  (integrable_countingProcess hT hC t).sub (integrable_compensator hT hC hind t)

/-- The compensated process is adapted to the history filtration. -/
theorem measurable_compensatedProcess_history (Λ : Measure ℝ) (t : ℝ) :
    Measurable[historyFiltration hT hC t] (compensatedProcess T C Λ t) :=
  (measurable_countingProcess_history hT hC le_rfl).sub
    ((measurable_compensator_strictPast hT hC Λ t).mono (strictPast_le_history hT hC t) le_rfl)

/-- **Orthogonality of martingale increments to the past**: for `a ≤ b` and every event `A`
observed by time `a`, `∫_A (M(b) - M(a)) dP = 0`. On `A ∩ {X ≤ a}` the increment vanishes
pathwise; by `history_inter_or_subset` the rest of `A` is either empty or all of `{X > a}`, where
the identity is `E N(b) - E N(a) = E A(b) - E A(a)`. -/
theorem setIntegral_compensatedProcess_sub_eq_zero [IsProbabilityMeasure μ]
    (hind : IndepFun T C μ) {a b : ℝ} (hab : a ≤ b) {A : Set Ω}
    (hA : MeasurableSet[historyFiltration hT hC a] A) :
    ∫ ω in A, (compensatedProcess T C (hazardMeasure (μ.map T)) b ω -
      compensatedProcess T C (hazardMeasure (μ.map T)) a ω) ∂μ = 0 := by
  set Λ := hazardMeasure (μ.map T) with hΛ
  have hzero : ∀ ω, ¬ a < obsTime T C ω →
      compensatedProcess T C Λ b ω - compensatedProcess T C Λ a ω = 0 := fun ω hω => by
    have hXa : obsTime T C ω ≤ a := not_lt.1 hω
    simp only [compensatedProcess]
    rw [countingProcess_of_obsTime_le (hXa.trans hab), countingProcess_of_obsTime_le hXa,
      compensator_eq, compensator_eq, min_eq_right (hXa.trans hab), min_eq_right hXa]
    ring
  rcases history_inter_or_subset hT hC hA with h | h
  · exact setIntegral_eq_zero_of_forall_eq_zero fun ω hω => hzero ω fun hE =>
      (h.subset ⟨hω, hE⟩ : ω ∈ (∅ : Set Ω))
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun ω hω => hzero ω fun hE => hω (h hE),
      integral_sub (integrable_compensatedProcess hT hC hind b)
        (integrable_compensatedProcess hT hC hind a)]
    simp only [compensatedProcess]
    rw [integral_sub (integrable_countingProcess hT hC b) (integrable_compensator hT hC hind b),
      integral_sub (integrable_countingProcess hT hC a) (integrable_compensator hT hC hind a),
      integral_countingProcess_eq_integral_compensator hT hC hind b,
      integral_countingProcess_eq_integral_compensator hT hC hind a]
    ring

/-- A process whose increments integrate to zero over every past event of a filtration is a
martingale for it (continuous-time form of `martingale_of_setIntegral_eq_succ`). -/
private lemma martingale_of_setIntegral_sub_eq_zero [IsProbabilityMeasure μ] {ℱ : Filtration ℝ m0}
    {M : ℝ → Ω → ℝ} (hadapt : StronglyAdapted ℱ M) (hint : ∀ t, Integrable (M t) μ)
    (h : ∀ a b, a ≤ b → ∀ A, MeasurableSet[ℱ a] A → ∫ ω in A, (M b ω - M a ω) ∂μ = 0) :
    Martingale M ℱ μ := by
  refine ⟨hadapt, fun a b hab => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) (hint b)
    (fun s _ _ => (hint a).integrableOn) (fun s hs _ => ?_) (hadapt a).aestronglyMeasurable).symm
  have := h a b hab s hs
  rw [integral_sub (hint b).integrableOn (hint a).integrableOn] at this
  linarith

/-- **Compensator identity (martingale form)**. In the random-censorship model with latent failure
time `T` independent of the censoring time `C`, the compensated counting process
`M(t) = N(t) - ∫_{(-∞, t]} Y dΛ`, with `Λ` the hazard measure of the law of `T`, is a martingale
for the history filtration `ℱₜ = σ(N(u), Nᶜ(u) : u ≤ t)`. So `A(t) = ∫_{(-∞, t]} Y dΛ`, which is
`ℱ_{t-}`-measurable (`measurable_compensator_strictPast`), is a compensator of `N` in the sense
that `N - A` is a martingale and `A(t)` is `ℱ_{t-}`-measurable (uniqueness is not proved), and the
intensity is `Y(t) dΛ(t)` (`Y(t) λ(t) dt` when `T` has a density, `hazardMeasure_withDensity`). -/
theorem martingale_compensatedProcess [IsProbabilityMeasure μ] (hind : IndepFun T C μ) :
    Martingale (compensatedProcess T C (hazardMeasure (μ.map T))) (historyFiltration hT hC) μ :=
  martingale_of_setIntegral_sub_eq_zero
    (fun t => (measurable_compensatedProcess_history hT hC _ t).stronglyMeasurable)
    (integrable_compensatedProcess hT hC hind)
    fun _ _ hab _ hA => setIntegral_compensatedProcess_sub_eq_zero hT hC hind hab hA

omit hT hC in
/-- The history of one subject is generated by its pair `(T, C)` of latent times. -/
theorem historyFiltration_le_comap (hT : Measurable T) (hC : Measurable C) (t : ℝ) :
    historyFiltration hT hC t ≤
      MeasurableSpace.comap (fun ω => (T ω, C ω)) inferInstance := by
  refine iSup₂_le fun u _ => ?_
  have hψ : Measurable (observedProcess (Prod.fst : ℝ × ℝ → ℝ) Prod.snd u) :=
    (stronglyMeasurable_observedProcess measurable_fst measurable_snd u).measurable
  have : observedProcess T C u = observedProcess (Prod.fst : ℝ × ℝ → ℝ) Prod.snd u ∘
      fun ω => (T ω, C ω) := rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hψ.comap_le

/-! ### Several independent subjects -/

/-- If `f` is `m_f`-measurable with `∫_G f = 0` for every `G ∈ 𝒢 ≤ m_f`, and `ℋ` is independent
of `m_f`, then `∫_A f = 0` for every `A ∈ 𝒢 ⊔ ℋ`: enlarging the past by independent information
preserves the orthogonality. -/
private lemma setIntegral_eq_zero_of_indep_sup [IsProbabilityMeasure μ]
    {mf 𝒢 ℋ : MeasurableSpace Ω} (hmf : mf ≤ m0) (h𝒢 : 𝒢 ≤ mf) (hℋ : ℋ ≤ m0)
    (hind : Indep mf ℋ μ) {f : Ω → ℝ} (hfm : StronglyMeasurable[mf] f) (hfi : Integrable f μ)
    (h0 : ∀ G, MeasurableSet[𝒢] G → ∫ ω in G, f ω ∂μ = 0) :
    ∀ A, MeasurableSet[𝒢 ⊔ ℋ] A → ∫ ω in A, f ω ∂μ = 0 := by
  set P : Set (Set Ω) := image2 (· ∩ ·) {s | MeasurableSet[𝒢] s} {s | MeasurableSet[ℋ] s}
  have hle : 𝒢 ⊔ ℋ ≤ m0 := sup_le (h𝒢.trans hmf) hℋ
  have hP : IsPiSystem P := by
    rintro _ ⟨G₁, hG₁, H₁, hH₁, rfl⟩ _ ⟨G₂, hG₂, H₂, hH₂, rfl⟩ -
    refine ⟨G₁ ∩ G₂, MeasurableSet.inter hG₁ hG₂, H₁ ∩ H₂, MeasurableSet.inter hH₁ hH₂, ?_⟩
    simp only
    ext x; simp only [mem_inter_iff]; tauto
  have hgen : 𝒢 ⊔ ℋ = MeasurableSpace.generateFrom P := by
    refine le_antisymm (sup_le (fun G hG => ?_) fun H hH => ?_) (MeasurableSpace.generateFrom_le ?_)
    · exact MeasurableSpace.measurableSet_generateFrom ⟨G, hG, univ, MeasurableSet.univ,
        inter_univ G⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨univ, MeasurableSet.univ, H, hH,
        univ_inter H⟩
    · rintro _ ⟨G, hG, H, hH, rfl⟩
      exact ((le_sup_left : 𝒢 ≤ 𝒢 ⊔ ℋ) _ hG).inter ((le_sup_right : ℋ ≤ 𝒢 ⊔ ℋ) _ hH)
  have hf0 : ∫ ω, f ω ∂μ = 0 := by
    simpa using h0 univ MeasurableSet.univ
  refine MeasurableSpace.induction_on_inter (C := fun A _ => ∫ ω in A, f ω ∂μ = 0) hgen hP
    (by simp) ?_ ?_ ?_
  · rintro _ ⟨G, hG, H, hH, rfl⟩
    have hGm : MeasurableSet[m0] G := hmf _ (h𝒢 _ hG)
    have hgm : StronglyMeasurable[mf] (G.indicator f) := hfm.indicator (h𝒢 _ hG)
    have hgi : Integrable (G.indicator f) μ := hfi.indicator hGm
    have hce := condExp_indep_eq hmf hℋ hgm hind
    change ∫ ω in G ∩ H, f ω ∂μ = 0
    rw [inter_comm, ← setIntegral_indicator hGm, ← setIntegral_condExp hℋ hgi hH,
      setIntegral_congr_ae (hℋ _ hH) (hce.mono fun ω hω _ => hω), setIntegral_const,
      integral_indicator hGm, h0 G hG, smul_zero]
  · intro A hA hA0
    have hAm : MeasurableSet[m0] A := hle _ hA
    have := integral_add_compl hAm hfi
    rw [hA0, hf0, zero_add] at this
    exact this
  · intro g hdisj hgm hg0
    rw [integral_iUnion (fun i => hle _ (hgm i)) hdisj hfi.integrableOn]
    simp [hg0]

variable {ι : Type*} {Ts Cs : ι → Ω → ℝ}

/-- The **joint history filtration** `ℱₜ = ⋁ᵢ σ(Nᵢ(u), Nᶜᵢ(u) : u ≤ t)` of several subjects. -/
noncomputable def jointHistoryFiltration (hT : ∀ i, Measurable (Ts i))
    (hC : ∀ i, Measurable (Cs i)) : Filtration ℝ m0 where
  seq t := ⨆ i, historyFiltration (hT i) (hC i) t
  mono' _ _ hst := iSup_mono fun i => (historyFiltration (hT i) (hC i)).mono hst
  le' t := iSup_le fun i => (historyFiltration (hT i) (hC i)).le t

/-- **Compensator identity for one subject in a cohort**. If the pairs `(Tᵢ, Cᵢ)` are mutually
independent and `Tᵢ ⊥ Cᵢ` for each `i`, the compensated process of subject `i` is a martingale
for the joint history filtration of all subjects (the other subjects' histories carry no
information about subject `i`). -/
theorem martingale_compensatedProcess_joint [IsProbabilityMeasure μ]
    (hTs : ∀ i, Measurable (Ts i)) (hCs : ∀ i, Measurable (Cs i))
    (hpair : iIndepFun (fun i ω => (Ts i ω, Cs i ω)) μ) (hind : ∀ i, IndepFun (Ts i) (Cs i) μ)
    (i : ι) :
    Martingale (compensatedProcess (Ts i) (Cs i) (hazardMeasure (μ.map (Ts i))))
      (jointHistoryFiltration hTs hCs) μ := by
  set m : ι → MeasurableSpace Ω :=
    fun j => MeasurableSpace.comap (fun ω => (Ts j ω, Cs j ω)) inferInstance with hm
  have hmle : ∀ j, m j ≤ m0 := fun j => ((hTs j).prodMk (hCs j)).comap_le
  have hiind : iIndep m μ := (iIndepFun_iff_iIndep _ _ μ).1 hpair
  have hindep : Indep (m i) (⨆ j ∈ ({i}ᶜ : Set ι), m j) μ := by
    have := indep_iSup_of_disjoint hmle hiind (S := {i}) (T := {i}ᶜ) disjoint_compl_right
    simpa using this
  refine martingale_of_setIntegral_sub_eq_zero
    (fun t => ((measurable_compensatedProcess_history (hTs i) (hCs i) _ t).mono
      (le_iSup (fun j => historyFiltration (hTs j) (hCs j) t) i) le_rfl).stronglyMeasurable)
    (integrable_compensatedProcess (hTs i) (hCs i) (hind i)) fun a b hab A hA => ?_
  have hsplit : jointHistoryFiltration hTs hCs a ≤ historyFiltration (hTs i) (hCs i) a ⊔
      ⨆ j ∈ ({i}ᶜ : Set ι), historyFiltration (hTs j) (hCs j) a := by
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · subst hj; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ∈ ({i}ᶜ : Set ι)) =>
        historyFiltration (hTs j) (hCs j) a) j hj)
  refine setIntegral_eq_zero_of_indep_sup (hmle i)
    (historyFiltration_le_comap (hTs i) (hCs i) a)
    (iSup₂_le fun j _ => (historyFiltration (hTs j) (hCs j)).le a)
    (indep_of_indep_of_le_right hindep (iSup₂_mono fun j _ =>
      historyFiltration_le_comap (hTs j) (hCs j) a))
    ((((measurable_compensatedProcess_history (hTs i) (hCs i) _ b).mono
      (historyFiltration_le_comap (hTs i) (hCs i) b) le_rfl).sub
      ((measurable_compensatedProcess_history (hTs i) (hCs i) _ a).mono
      (historyFiltration_le_comap (hTs i) (hCs i) a) le_rfl)).stronglyMeasurable)
    ((integrable_compensatedProcess (hTs i) (hCs i) (hind i) b).sub
      (integrable_compensatedProcess (hTs i) (hCs i) (hind i) a))
    (fun G hG => setIntegral_compensatedProcess_sub_eq_zero (hTs i) (hCs i) (hind i) hab hG)
    A (hsplit A hA)

variable [Fintype ι]

/-- The **aggregated counting process** `N(t) = ∑ᵢ Nᵢ(t)`: observed failures by time `t`. -/
noncomputable def totalCountingProcess (Ts Cs : ι → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, countingProcess (Ts i) (Cs i) t ω

/-- The **number at risk** `Y(t) = ∑ᵢ Yᵢ(t)`. -/
noncomputable def totalAtRiskProcess (Ts Cs : ι → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, atRiskProcess (Ts i) (Cs i) t ω

/-- The **aggregated compensator** `A(t) = ∑ᵢ ∫_{(-∞, t]} Yᵢ dΛᵢ`, with `Λᵢ` the hazard measure of
the law of `Tᵢ`. For a common law, `A(t) = ∫_{(-∞, t]} Y dΛ` (`totalCompensator_eq_of_map_eq`):
Aalen's multiplicative intensity `Y(t) dΛ(t)`. -/
noncomputable def totalCompensator (μ : Measure Ω) (Ts Cs : ι → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i, compensator (Ts i) (Cs i) (hazardMeasure (μ.map (Ts i))) t ω

/-- Linearity of the at-risk integral for any measure `Λ`:
`∫_{(-∞, t]} Y dΛ = ∑ᵢ ∫_{(-∞, t]} Yᵢ dΛ` with `Y` the number at risk. -/
theorem lintegral_totalAtRiskProcess (Λ : Measure ℝ) (t : ℝ) (ω : Ω) :
    ∫⁻ s in Iic t, ENNReal.ofReal (totalAtRiskProcess Ts Cs s ω) ∂Λ =
      ∑ i, ∫⁻ s in Iic t, ENNReal.ofReal (atRiskProcess (Ts i) (Cs i) s ω) ∂Λ := by
  simp only [totalAtRiskProcess]
  have hnn : ∀ s i, 0 ≤ atRiskProcess (Ts i) (Cs i) s ω := fun s i => by
    rcases atRiskProcess_mem (T := Ts i) (C := Cs i) s ω with h | h <;> simp_all
  simp_rw [ENNReal.ofReal_sum_of_nonneg fun i _ => hnn _ i]
  refine lintegral_finsetSum' _ fun i _ => ?_
  have : (fun s => atRiskProcess (Ts i) (Cs i) s ω) = (Iic (obsTime (Ts i) (Cs i) ω)).indicator 1 :=
    funext fun s => atRiskProcess_eq_indicator s ω
  exact (Measurable.ennreal_ofReal (this ▸ measurable_one.indicator measurableSet_Iic)).aemeasurable

/-- **Multiplicative intensity** for a common law: if every `Tᵢ` has law `F`, the aggregated
compensator is `∫_{(-∞, t]} Y dΛ` with `Y` the number at risk and `Λ` the hazard measure of `F`
(Aalen's model). The finiteness hypothesis holds almost surely under the model
(`lintegral_hazardMeasure_Iic_obsTime_lt_top`). -/
theorem totalCompensator_eq_of_map_eq {μ : Measure Ω} {F : Measure ℝ}
    (hlaw : ∀ i, μ.map (Ts i) = F) (t : ℝ) (ω : Ω)
    (hfin : ∀ i, ∫⁻ s in Iic t, ENNReal.ofReal (atRiskProcess (Ts i) (Cs i) s ω)
      ∂(hazardMeasure F) ≠ ∞) :
    totalCompensator μ Ts Cs t ω =
      (∫⁻ s in Iic t, ENNReal.ofReal (totalAtRiskProcess Ts Cs s ω) ∂(hazardMeasure F)).toReal := by
  rw [lintegral_totalAtRiskProcess, ENNReal.toReal_sum fun i _ => hfin i]
  simp only [totalCompensator, compensator, hlaw]

/-- **Compensator identity for the aggregated process**. With mutually independent subjects and
independent censoring within each subject, `N(t) - A(t) = ∑ᵢ (Nᵢ(t) - Aᵢ(t))` is a martingale
for the joint history filtration. -/
theorem martingale_totalCountingProcess_sub_totalCompensator [IsProbabilityMeasure μ]
    (hTs : ∀ i, Measurable (Ts i)) (hCs : ∀ i, Measurable (Cs i))
    (hpair : iIndepFun (fun i ω => (Ts i ω, Cs i ω)) μ) (hind : ∀ i, IndepFun (Ts i) (Cs i) μ) :
    Martingale (fun t ω => totalCountingProcess Ts Cs t ω - totalCompensator μ Ts Cs t ω)
      (jointHistoryFiltration hTs hCs) μ := by
  have heq : (fun t ω => totalCountingProcess Ts Cs t ω - totalCompensator μ Ts Cs t ω) =
      ∑ i, compensatedProcess (Ts i) (Cs i) (hazardMeasure (μ.map (Ts i))) := by
    classical
    funext t ω
    simp [totalCountingProcess, totalCompensator, compensatedProcess, Finset.sum_sub_distrib]
  rw [heq]
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simpa using martingale_zero (E := ℝ) (jointHistoryFiltration hTs hCs) μ
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact (martingale_compensatedProcess_joint hTs hCs hpair hind j).add ih

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
