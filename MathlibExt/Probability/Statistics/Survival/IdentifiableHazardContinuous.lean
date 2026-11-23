/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CountingProcess
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Identification of the hazard up to the censoring horizon, continuous time

Under independent right censoring one observes `X = T ∧ C` and `δ = 1{T ≤ C}` for a failure time
`T` with law `F` and a censoring time `C` with law `G`. This file shows that the law of `(X, δ)`
identifies `F`, and hence the hazard measure `dΛ = dF / F[s, ∞)`, exactly on the set of times at
which subjects can still be under observation, and nothing beyond it. It is the continuous-time
counterpart of the grid statement `Censoring.censoredObsLaw_indepLaw_eq_iff` in
`IdentifiableHorizon`.

## Definitions

* `censoredObsMap`: `(t, c) ↦ (t ∧ c, 1{t ≤ c})` (ties count as failures, as in `countingProcess`);
  its first coordinate is `obsTime`.
* `censoredObsLaw F G`: the observed-data law, the image of `F ⊗ G` under `censoredObsMap`.
* `observableSet G = {s | G[s, ∞) ≠ 0}`: the times `s` at which a subject failing at `s` can be
  observed to fail. It is a down-set (`observableSet_downward`): `(-∞, τ]` or `(-∞, τ)` for the
  right end `τ` of the support of `G`, all of `ℝ` if the support is unbounded above, and `∅`
  when `G = 0`.

## Main results

* `censoredObsLaw_apply_prod_true`, `censoredObsLaw_apply_prod_false`: the observed sub-densities
  `P(X ∈ A, δ = 1) = ∫_A G[t, ∞) dF(t)` and `P(X ∈ B, δ = 0) = ∫_B F(c, ∞) dG(c)`.
* `censoredObsLaw_eq_iff`: two failure-time laws give the same observed-data law if and only if
  they agree on `observableSet G`.
* `restrict_Iic_eq_of_censoredObsLaw_eq`: if `G[h, ∞) ≠ 0`, the observed-data law determines
  `F` on `(-∞, h]`.
* `hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq`,
  `hazardMeasure_restrict_Ico_eq_of_censoredObsLaw_eq`, `hazardMeasure_Iic_eq_of_censoredObsLaw_eq`:
  **the hazard is identified up to the horizon**: if `G[h, ∞) ≠ 0`, the observed-data law
  determines the hazard measure on `(-∞, h]`, in particular on `[0, h)` and the cumulative hazard
  `Λ(-∞, t]` for `t ≤ h`.
* `censoredObsLaw_eq_of_restrict_Iic_eq`: conversely, if `G(h, ∞) = 0`, any two failure-time
  laws that agree on `(-∞, h]` give the same observed-data law, so nothing beyond `h` is
  identified.
* `map_obs_eq_censoredObsLaw`: for random variables `T ⊥ C` on a probability space, the law of
  `(obsTime T C, 1{T ≤ C})` is `censoredObsLaw (law T) (law C)`, so the results apply to the model
  of `CountingProcess`.

## Scope

The statement is for a single subject's observed-data law under independent censoring
(`T ⊥ C`); `F` and `G` are arbitrary Borel probability laws on `ℝ` (atoms allowed, no support
condition). For i.i.d. subjects the sample law is the product of single-subject laws, so equality
transfers to the sample; that transfer and estimation (Nelson–Aalen, Kaplan–Meier consistency in
continuous time) are not treated here. Times are on `ℝ`; nonnegativity of `T` plays no role.

## Reused API (source receipts)

* `CountingProcess.ContinuousTime.obsTime`, `hazardMeasure`, `measurable_measure_Ici`,
  `ae_measure_Ici_ne_zero` (`MathlibExt/Probability/Statistics/Survival/CountingProcess.lean`).
* `MeasureTheory.Measure.prod_apply`, `Measure.prod_apply_symm`
  (`Mathlib/MeasureTheory/Measure/Prod.lean`); `MeasureTheory.withDensity_inv_same`,
  `restrict_withDensity` (`Mathlib/MeasureTheory/Measure/WithDensity.lean`);
  `ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`
  (`Mathlib/Probability/Independence/Basic.lean`).

## References

* A. Tsiatis, *A nonidentifiability aspect of the problem of competing risks*, Proc. Natl. Acad.
  Sci. USA 72 (1975), 20–22 (identifiability of the marginal law under independent censoring).
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Section III.2.2 (independent censoring; the hazard is identified
  on `{s : P(X ≥ s) > 0}`). That set is `observableSet G ∩ {s | F[s, ∞) ≠ 0}`; it differs from
  `observableSet G` only where `F[s, ∞) = 0`, which does not affect the hazard.
* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Section 1.2 (identifiability under independent censoring) and Section 3.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-! ### The observation map and the observed-data law -/

/-- The **observation map** of right-censored data in continuous time: from the failure and
censoring times `(t, c)` one observes `obsTime = t ∧ c` and the failure flag `1{t ≤ c}` (ties
count as failures, as in `countingProcess`). -/
noncomputable def censoredObsMap (ω : ℝ × ℝ) : ℝ × Bool :=
  (obsTime Prod.fst Prod.snd ω, decide (ω.1 ≤ ω.2))

/-- The **observed-data law** of right-censored data under independent censoring: the law of
`(T ∧ C, 1{T ≤ C})` when `T ~ F` and `C ~ G` are independent. -/
noncomputable def censoredObsLaw (F G : Measure ℝ) : Measure (ℝ × Bool) :=
  (F.prod G).map censoredObsMap

/-- The **observable set** of the censoring law `G`: the times `s` with `G[s, ∞) ≠ 0`, at which
a subject failing at `s` is still under observation with positive probability. -/
def observableSet (G : Measure ℝ) : Set ℝ := {s | G (Ici s) ≠ 0}

/-- The observation map is measurable. -/
theorem measurable_censoredObsMap : Measurable censoredObsMap := by
  refine Measurable.prodMk (measurable_fst.min measurable_snd) (measurable_to_bool ?_)
  have : (fun ω : ℝ × ℝ => decide (ω.1 ≤ ω.2)) ⁻¹' {true} = {ω | ω.1 ≤ ω.2} := by ext; simp
  rw [this]
  exact measurableSet_le measurable_fst measurable_snd

/-- The observable set is measurable. -/
theorem measurableSet_observableSet (G : Measure ℝ) : MeasurableSet (observableSet G) :=
  (measurable_measure_Ici G) (measurableSet_singleton 0).compl

/-- The observable set is a down-set: a subject observable at `s` is observable at every
earlier time. -/
theorem observableSet_downward {G : Measure ℝ} {s s' : ℝ} (hs : s ∈ observableSet G)
    (hs' : s' ≤ s) : s' ∈ observableSet G :=
  fun h0 => hs (measure_mono_null (Ici_subset_Ici.2 hs') h0)

/-- If the censoring law has positive mass at or after `h`, every time up to `h` is
observable. -/
theorem Iic_subset_observableSet {G : Measure ℝ} {h : ℝ} (hG : G (Ici h) ≠ 0) :
    Iic h ⊆ observableSet G :=
  fun _ hs => observableSet_downward hG hs

/-- If the censoring law puts no mass after `h`, nothing after `h` is observable. -/
theorem observableSet_subset_Iic {G : Measure ℝ} {h : ℝ} (hG : G (Ioi h) = 0) :
    observableSet G ⊆ Iic h := by
  intro s hs
  by_contra hsh
  exact hs (measure_mono_null (Ici_subset_Ioi.2 (not_le.1 hsh)) hG)

/-- **Observed failures**: `P(X ∈ A, δ = 1) = ∫_A G[t, ∞) dF(t)`. -/
theorem censoredObsLaw_apply_prod_true (F G : Measure ℝ) [SFinite G] {A : Set ℝ}
    (hA : MeasurableSet A) :
    censoredObsLaw F G (A ×ˢ {true}) = ∫⁻ t in A, G (Ici t) ∂F := by
  have hpre : censoredObsMap ⁻¹' (A ×ˢ {true}) = {ω : ℝ × ℝ | ω.1 ∈ A ∧ ω.1 ≤ ω.2} := by
    ext ⟨t, c⟩
    simp only [censoredObsMap, obsTime, mem_preimage, mem_prod, mem_singleton_iff,
      decide_eq_true_eq, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [min_eq_left h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [min_eq_left h2]
      exact ⟨h1, h2⟩
  have hmeas : MeasurableSet {ω : ℝ × ℝ | ω.1 ∈ A ∧ ω.1 ≤ ω.2} :=
    (measurable_fst hA).inter (measurableSet_le measurable_fst measurable_snd)
  rw [censoredObsLaw, Measure.map_apply measurable_censoredObsMap (hA.prod (by simp)), hpre,
    Measure.prod_apply hmeas, ← lintegral_indicator hA]
  congr 1
  funext t
  by_cases ht : t ∈ A
  · rw [indicator_of_mem ht]
    congr 1
    ext c
    simp [ht]
  · rw [indicator_of_notMem ht]
    convert measure_empty (μ := G)
    ext c
    simp [ht]

/-- **Observed censorings**: `P(X ∈ B, δ = 0) = ∫_B F(c, ∞) dG(c)`. -/
theorem censoredObsLaw_apply_prod_false (F G : Measure ℝ) [SFinite F] [SFinite G] {B : Set ℝ}
    (hB : MeasurableSet B) :
    censoredObsLaw F G (B ×ˢ {false}) = ∫⁻ c in B, F (Ioi c) ∂G := by
  have hpre : censoredObsMap ⁻¹' (B ×ˢ {false}) = {ω : ℝ × ℝ | ω.2 ∈ B ∧ ω.2 < ω.1} := by
    ext ⟨t, c⟩
    simp only [censoredObsMap, obsTime, mem_preimage, mem_prod, mem_singleton_iff,
      decide_eq_false_iff_not, not_le, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [min_eq_right h2.le] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [min_eq_right h2.le]
      exact ⟨h1, h2⟩
  have hmeas : MeasurableSet {ω : ℝ × ℝ | ω.2 ∈ B ∧ ω.2 < ω.1} :=
    (measurable_snd hB).inter (measurableSet_lt measurable_snd measurable_fst)
  rw [censoredObsLaw, Measure.map_apply measurable_censoredObsMap (hB.prod (by simp)), hpre,
    Measure.prod_apply_symm hmeas, ← lintegral_indicator hB]
  congr 1
  funext c
  by_cases hc : c ∈ B
  · rw [indicator_of_mem hc]
    congr 1
    ext t
    simp [hc]
  · rw [indicator_of_notMem hc]
    convert measure_empty (μ := F)
    ext t
    simp [hc]

/-- A measure on `ℝ × Bool` is determined by its values on the sets `A ×ˢ {true}` and
`B ×ˢ {false}`. -/
private lemma measure_ext_prod_bool {μ ν : Measure (ℝ × Bool)}
    (htrue : ∀ A, MeasurableSet A → μ (A ×ˢ {true}) = ν (A ×ˢ {true}))
    (hfalse : ∀ B, MeasurableSet B → μ (B ×ˢ {false}) = ν (B ×ˢ {false})) : μ = ν := by
  ext S hS
  have hsec : ∀ b : Bool, MeasurableSet {t : ℝ | (t, b) ∈ S} := fun b =>
    measurable_prodMk_right hS
  have hS_eq : S = {t : ℝ | (t, true) ∈ S} ×ˢ {true} ∪ {t : ℝ | (t, false) ∈ S} ×ˢ {false} := by
    ext ⟨t, b⟩
    cases b <;> simp
  have hdisj : Disjoint ({t : ℝ | (t, true) ∈ S} ×ˢ ({true} : Set Bool))
      ({t : ℝ | (t, false) ∈ S} ×ˢ {false}) :=
    disjoint_prod.2 (Or.inr (by simp))
  rw [hS_eq, measure_union hdisj ((hsec false).prod (by simp)),
    measure_union hdisj ((hsec false).prod (by simp)), htrue _ (hsec true),
    hfalse _ (hsec false)]

/-! ### Identification of the failure-time law -/

variable {F F' G : Measure ℝ}

/-- The observed-failure part of the observed-data law is `F` with density `G[t, ∞)`. -/
private lemma withDensity_eq_of_censoredObsLaw_eq [SFinite G]
    (heq : censoredObsLaw F G = censoredObsLaw F' G) :
    F.withDensity (fun t => G (Ici t)) = F'.withDensity (fun t => G (Ici t)) := by
  ext A hA
  rw [withDensity_apply _ hA, withDensity_apply _ hA, ← censoredObsLaw_apply_prod_true F G hA,
    ← censoredObsLaw_apply_prod_true F' G hA, heq]

/-- **The observed-data law identifies the failure-time law on the observable set.** -/
theorem restrict_observableSet_eq_of_censoredObsLaw_eq [IsFiniteMeasure G]
    (heq : censoredObsLaw F G = censoredObsLaw F' G) :
    F.restrict (observableSet G) = F'.restrict (observableSet G) := by
  set S := observableSet G
  have hS := measurableSet_observableSet G
  have hg := measurable_measure_Ici G
  have hne0 : ∀ μ : Measure ℝ, ∀ᵐ t ∂μ.restrict S, G (Ici t) ≠ 0 := fun μ =>
    (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun _ ht => ht)
  have hnetop : ∀ μ : Measure ℝ, ∀ᵐ t ∂μ.restrict S, G (Ici t) ≠ ∞ := fun μ =>
    Filter.Eventually.of_forall fun _ => measure_ne_top _ _
  calc F.restrict S
      = ((F.restrict S).withDensity fun t => G (Ici t)).withDensity fun t => (G (Ici t))⁻¹ :=
        (withDensity_inv_same hg (hne0 F) (hnetop F)).symm
    _ = ((F.withDensity fun t => G (Ici t)).restrict S).withDensity fun t => (G (Ici t))⁻¹ := by
        rw [restrict_withDensity hS]
    _ = ((F'.withDensity fun t => G (Ici t)).restrict S).withDensity fun t => (G (Ici t))⁻¹ := by
        rw [withDensity_eq_of_censoredObsLaw_eq heq]
    _ = ((F'.restrict S).withDensity fun t => G (Ici t)).withDensity fun t => (G (Ici t))⁻¹ := by
        rw [restrict_withDensity hS]
    _ = F'.restrict S := withDensity_inv_same hg (hne0 F') (hnetop F')

/-- **Agreement on the observable set gives the same observed-data law.** -/
theorem censoredObsLaw_eq_of_restrict_observableSet_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G]
    (hF : F.restrict (observableSet G) = F'.restrict (observableSet G)) :
    censoredObsLaw F G = censoredObsLaw F' G := by
  have hS := measurableSet_observableSet G
  refine measure_ext_prod_bool (fun A hA => ?_) (fun B hB => ?_)
  · -- the integrand `G[t, ∞)` vanishes off the observable set
    rw [censoredObsLaw_apply_prod_true F G hA, censoredObsLaw_apply_prod_true F' G hA]
    have hind : (fun t => G (Ici t)) = (observableSet G).indicator (fun t => G (Ici t)) := by
      funext t
      by_cases ht : t ∈ observableSet G
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht]
        simpa [observableSet] using ht
    rw [hind, lintegral_indicator hS, lintegral_indicator hS, Measure.restrict_restrict hS,
      Measure.restrict_restrict hS,
      ← Measure.restrict_restrict_of_subset (μ := F) inter_subset_left,
      ← Measure.restrict_restrict_of_subset (μ := F') inter_subset_left, hF]
  · -- `G`-almost every censoring time is observable, and there `F(c, ∞)` is determined
    rw [censoredObsLaw_apply_prod_false F G hB, censoredObsLaw_apply_prod_false F' G hB]
    refine setLIntegral_congr_fun_ae hB ?_
    filter_upwards [ae_measure_Ici_ne_zero G] with c hc _
    have hIic : F (Iic c) = F' (Iic c) := by
      rw [← Measure.restrict_eq_self F (Iic_subset_observableSet hc),
        ← Measure.restrict_eq_self F' (Iic_subset_observableSet hc), hF]
    rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top _ _),
      measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, measure_univ, hIic]

/-- **Exact identification.** Under independent censoring with censoring law `G`, two
failure-time laws give the same observed-data law if and only if they agree on the observable
set `{s | G[s, ∞) ≠ 0}`. -/
theorem censoredObsLaw_eq_iff [IsProbabilityMeasure F] [IsProbabilityMeasure F']
    [IsFiniteMeasure G] :
    censoredObsLaw F G = censoredObsLaw F' G ↔
      F.restrict (observableSet G) = F'.restrict (observableSet G) :=
  ⟨restrict_observableSet_eq_of_censoredObsLaw_eq,
    censoredObsLaw_eq_of_restrict_observableSet_eq⟩

/-- **Identification up to the horizon.** If the censoring law has positive mass at or after `h`,
the observed-data law determines the failure-time law on `(-∞, h]`. -/
theorem restrict_Iic_eq_of_censoredObsLaw_eq [IsFiniteMeasure G] {h : ℝ} (hG : G (Ici h) ≠ 0)
    (heq : censoredObsLaw F G = censoredObsLaw F' G) :
    F.restrict (Iic h) = F'.restrict (Iic h) := by
  rw [← Measure.restrict_restrict_of_subset (Iic_subset_observableSet hG),
    ← Measure.restrict_restrict_of_subset (Iic_subset_observableSet hG) (μ := F'),
    restrict_observableSet_eq_of_censoredObsLaw_eq heq]

/-- **Nothing beyond the horizon is identified.** If the censoring law puts no mass after `h`,
two failure-time laws that agree on `(-∞, h]` give the same observed-data law, however they
distribute the mass `P(T > h)`. -/
theorem censoredObsLaw_eq_of_restrict_Iic_eq [IsProbabilityMeasure F] [IsProbabilityMeasure F']
    [IsFiniteMeasure G] {h : ℝ} (hG : G (Ioi h) = 0)
    (hF : F.restrict (Iic h) = F'.restrict (Iic h)) :
    censoredObsLaw F G = censoredObsLaw F' G := by
  refine censoredObsLaw_eq_of_restrict_observableSet_eq ?_
  rw [← Measure.restrict_restrict_of_subset (observableSet_subset_Iic hG),
    ← Measure.restrict_restrict_of_subset (observableSet_subset_Iic hG) (μ := F'), hF]

/-! ### Identification of the hazard -/

/-- Laws that agree on `(-∞, h]` give the same hazard measure on `(-∞, h]`: the density
`F[s, ∞)⁻¹` at `s ≤ h` only depends on `F(-∞, s)`. -/
theorem hazardMeasure_restrict_Iic_eq_of_restrict_Iic_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] {h : ℝ} (hF : F.restrict (Iic h) = F'.restrict (Iic h)) :
    (hazardMeasure F).restrict (Iic h) = (hazardMeasure F').restrict (Iic h) := by
  have hIci : ∀ s ∈ Iic h, F (Ici s) = F' (Ici s) := by
    intro s hs
    have hIio : F (Iio s) = F' (Iio s) := by
      have hsub : Iio s ⊆ Iic h := Iio_subset_Iic_self.trans (Iic_subset_Iic.2 hs)
      rw [← Measure.restrict_eq_self F hsub,
        ← Measure.restrict_eq_self F' hsub, hF]
    rw [← compl_Iio, measure_compl measurableSet_Iio (measure_ne_top _ _),
      measure_compl measurableSet_Iio (measure_ne_top _ _), measure_univ, measure_univ, hIio]
  rw [hazardMeasure, hazardMeasure, restrict_withDensity measurableSet_Iic,
    restrict_withDensity measurableSet_Iic, hF]
  refine withDensity_congr_ae ((ae_restrict_iff' measurableSet_Iic).2 ?_)
  exact Filter.Eventually.of_forall fun s hs => by simp only [hIci s hs]

/-- **The hazard is identified up to the horizon.** If the censoring law has positive mass at or
after `h`, the observed-data law determines the hazard measure `dΛ = dF / F[s, ∞)` on
`(-∞, h]`. -/
theorem hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G] {h : ℝ} (hG : G (Ici h) ≠ 0)
    (heq : censoredObsLaw F G = censoredObsLaw F' G) :
    (hazardMeasure F).restrict (Iic h) = (hazardMeasure F').restrict (Iic h) :=
  hazardMeasure_restrict_Iic_eq_of_restrict_Iic_eq (restrict_Iic_eq_of_censoredObsLaw_eq hG heq)

/-- **The hazard on `[0, h)` is identified** when the censoring law has positive mass at or after
`h`. -/
theorem hazardMeasure_restrict_Ico_eq_of_censoredObsLaw_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G] {h : ℝ} (hG : G (Ici h) ≠ 0)
    (heq : censoredObsLaw F G = censoredObsLaw F' G) :
    (hazardMeasure F).restrict (Ico 0 h) = (hazardMeasure F').restrict (Ico 0 h) := by
  have hsub : Ico 0 h ⊆ Iic h := Ico_subset_Icc_self.trans Icc_subset_Iic_self
  rw [← Measure.restrict_restrict_of_subset hsub,
    ← Measure.restrict_restrict_of_subset hsub (μ := hazardMeasure F'),
    hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq hG heq]

/-- **The cumulative hazard is identified up to the horizon**: `Λ(-∞, t] = Λ'(-∞, t]` for every
`t ≤ h` when `G[h, ∞) ≠ 0`. -/
theorem hazardMeasure_Iic_eq_of_censoredObsLaw_eq [IsProbabilityMeasure F]
    [IsProbabilityMeasure F'] [IsFiniteMeasure G] {h t : ℝ} (hG : G (Ici h) ≠ 0) (ht : t ≤ h)
    (heq : censoredObsLaw F G = censoredObsLaw F' G) :
    hazardMeasure F (Iic t) = hazardMeasure F' (Iic t) := by
  have hsub : Iic t ⊆ Iic h := Iic_subset_Iic.2 ht
  rw [← Measure.restrict_eq_self (hazardMeasure F) hsub,
    ← Measure.restrict_eq_self (hazardMeasure F') hsub,
    hazardMeasure_restrict_Iic_eq_of_censoredObsLaw_eq hG heq]

/-! ### The random-variable model -/

/-- For independent random variables `T ⊥ C`, the law of the observation `(T ∧ C, 1{T ≤ C})`
is the observed-data law of the laws of `T` and `C`. -/
theorem map_obs_eq_censoredObsLaw {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {T C : Ω → ℝ} (hT : Measurable T) (hC : Measurable C)
    (hind : IndepFun T C μ) :
    μ.map (fun ω => (obsTime T C ω, decide (T ω ≤ C ω))) =
      censoredObsLaw (μ.map T) (μ.map C) := by
  have hTC : Measurable fun ω => (T ω, C ω) := hT.prodMk hC
  rw [censoredObsLaw, ← (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable
    hC.aemeasurable).1 hind, Measure.map_map measurable_censoredObsMap hTC]
  rfl

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
