/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Censoring
public import MathlibExt.Probability.Statistics.Survival.Data
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw

/-!
# Consistency of the Kaplan–Meier estimator on a finite grid

Subjects `i = 0, 1, 2, …` have event and censoring times `(Tᵢ, Cᵢ) = Zᵢ` on the grid `Fin k`.
The `Zᵢ` are independent with a common law `μ` on `Fin k × Fin k`. From the first `n` subjects one
observes the follow-up index `Xᵢ = min Tᵢ Cᵢ` and the event flag `δᵢ = 1[Tᵢ ≤ Cᵢ]` (ties count as
events, as in `Censoring` and `KaplanMeier`). These give the grouped data
`empiricalData Z n ω = CensoredData.ofSubjects` at the grid times `j ↦ (j : ℝ)`.

## Main results

* `ae_tendsto_atRisk_div`, `ae_tendsto_deaths_div`: **per-cell strong law**: for any common law
  `μ`, almost surely `nⱼ / n → P(X ≥ j)` (`obsAtRiskMass μ j`) and
  `dⱼ / n → P(X = j, δ = 1)` (`obsEventMass μ j`).
* `prod_one_sub_hazard`: the discrete product-limit identity
  `∏_{j ≤ m} (1 - h(j)) = P(T > m)` for the hazard `h` of a law on the grid, provided
  `P(T ≥ m) ≠ 0`.
* `ae_tendsto_kmSurvival`: **consistency of Kaplan–Meier at grid times**: in the independent
  censoring model `μ = indepLaw pT pC`, if `P(X ≥ m) ≠ 0` then almost surely the Kaplan–Meier
  estimate at `m` converges to `P(T > m)`.
* `ae_tendsto_kmSurvival_infinitePi`: the same on the canonical sequence space
  `ℕ → Fin k × Fin k` with the product measure `Measure.infinitePi`.

## Scope

Independent censoring enters only through the identification theorem
`Censoring.obsEventMass_div_obsAtRiskMass`. The result concerns the survival function of `T` at
grid points `m` with positive at-risk mass; nothing is said about the tail beyond the support of
the censoring law, uniformity in `m`, or rates (no central limit theorem).

## References

* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Sections 1.2 and 3.2.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.SurvivalConsistency

open MeasureTheory ProbabilityTheory Filter Finset Topology Function
open MathlibExt.Probability.Statistics.Censoring MathlibExt.Probability.Statistics.KaplanMeier

variable {k : ℕ}

/-- The grid times `j ↦ (j : ℝ)` of `Fin k`. -/
def gridTime (j : Fin k) : ℝ := (j : ℕ)

theorem gridTime_strictMono : StrictMono (gridTime (k := k)) := fun _ _ h => by
  simpa [gridTime] using h

theorem gridTime_le_gridTime_iff {i j : Fin k} : gridTime i ≤ gridTime j ↔ i ≤ j :=
  gridTime_strictMono.le_iff_le

/-- The grouped censored data of the first `n` subjects of the sequence `Z`: subject `i` has
follow-up index `min Tᵢ Cᵢ` and event flag `Tᵢ ≤ Cᵢ`, where `(Tᵢ, Cᵢ) = Z i ω`. -/
def empiricalData {Ω : Type*} (Z : ℕ → Ω → Fin k × Fin k) (n : ℕ) (ω : Ω) : CensoredData k :=
  CensoredData.ofSubjects gridTime gridTime_strictMono (fun i : Fin n => min (Z i ω).1 (Z i ω).2)
    (fun i => decide ((Z i ω).1 ≤ (Z i ω).2))

/-! ### Per-cell strong law of large numbers -/

section SLLN

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
  [IsProbabilityMeasure P] {μ : Measure α}

omit [MeasurableSpace Ω] [MeasurableSpace α] in
open Classical in
/-- The counting identity: the number of `i < n` with `Z i ω ∈ s` is a sum of indicators. -/
private lemma card_filter_eq_sum_indicator (Z : ℕ → Ω → α) (s : Set α) (n : ℕ) (ω : Ω) :
    ((#{i : Fin n | Z i ω ∈ s} : ℕ) : ℝ) = ∑ i ∈ range n, s.indicator (1 : α → ℝ) (Z i ω) := by
  rw [natCast_card_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if Z i ω ∈ s then (1 : ℝ) else 0) n]
  simp [Set.indicator_apply]

open Classical in
/-- **Strong law for empirical frequencies**: for independent `Z i` with common law `μ`, the
fraction of the first `n` subjects in a measurable set `s` converges almost surely to `μ s`. -/
private theorem ae_tendsto_card_filter_div (Z : ℕ → Ω → α) (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) μ P) {s : Set α} (hs : MeasurableSet s) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ((#{i : Fin n | Z i ω ∈ s} : ℕ) : ℝ) / n) atTop
      (𝓝 (μ.real s)) := by
  set g : α → ℝ := s.indicator 1 with hg_def
  have hg : Measurable g := measurable_const.indicator hs
  set Y : ℕ → Ω → ℝ := fun i ω => g (Z i ω) with hY
  have hYint : Integrable (Y 0) P := by
    refine (integrable_const (1 : ℝ)).mono'
      (hg.comp_aemeasurable (hlaw 0).aemeasurable).aestronglyMeasurable ?_
    filter_upwards with ω
    by_cases h : Z 0 ω ∈ s <;> simp [hY, hg_def, h]
  have hpair : Pairwise ((· ⟂ᵢ[P] ·) on Y) := fun i j hij => (hind.indepFun hij).comp hg hg
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) P P := fun i =>
    (⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable, by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩ :
      IdentDistrib (Z i) (Z 0) P P).comp hg
  have hmean : P[Y 0] = μ.real s := by
    have := (hlaw 0).integral_comp (f := g) hg.aestronglyMeasurable
    rw [Function.comp_def] at this
    rw [hY, this, hg_def, integral_indicator_one hs]
  have H := strong_law_ae_real Y hYint hpair hident
  rw [hmean] at H
  filter_upwards [H] with ω hω
  refine hω.congr fun n => ?_
  rw [card_filter_eq_sum_indicator]

end SLLN

section Cells

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (Fin k × Fin k)} {Z : ℕ → Ω → Fin k × Fin k}

/-- **Per-cell strong law, at-risk counts**: for independent subjects `Zᵢ = (Tᵢ, Cᵢ)` with common
law `μ`, almost surely the at-risk proportion `nⱼ / n` converges to the observed at-risk mass
`P(min T C ≥ j)`. No independence between `T` and `C` is assumed. -/
theorem ae_tendsto_atRisk_div (hind : iIndepFun Z P) (hlaw : ∀ i, HasLaw (Z i) μ P)
    (j : Fin k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ((empiricalData Z n ω).atRisk j : ℝ) / n) atTop
      (𝓝 (obsAtRiskMass μ j)) := by
  classical
  filter_upwards [ae_tendsto_card_filter_div Z hind hlaw
    (s := {z : Fin k × Fin k | j ≤ min z.1 z.2}) (Set.toFinite _).measurableSet] with ω hω
  refine hω.congr fun n => ?_
  rw [empiricalData, CensoredData.atRisk_ofSubjects]
  congr 3
  ext i
  simp

/-- **Per-cell strong law, death counts**: for independent subjects `Zᵢ = (Tᵢ, Cᵢ)` with common
law `μ`, almost surely the death proportion `dⱼ / n` converges to the observed event mass
`P(min T C = j, T ≤ C)`. No independence between `T` and `C` is assumed. -/
theorem ae_tendsto_deaths_div (hind : iIndepFun Z P) (hlaw : ∀ i, HasLaw (Z i) μ P)
    (j : Fin k) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ((empiricalData Z n ω).deaths j : ℝ) / n) atTop
      (𝓝 (obsEventMass μ j)) := by
  classical
  filter_upwards [ae_tendsto_card_filter_div Z hind hlaw
    (s := {z : Fin k × Fin k | min z.1 z.2 = j ∧ z.1 ≤ z.2}) (Set.toFinite _).measurableSet]
    with ω hω
  refine hω.congr fun n => ?_
  rw [empiricalData, CensoredData.ofSubjects_deaths]
  congr 3
  ext i
  simp

end Cells

/-! ### The product-limit identity for a law on the grid -/

section ProductLimit

/-- `P(T ≥ j) = P(T = j) + P(T > j)`. -/
theorem survivalMass_eq_add (p : PMF (Fin k)) (j : Fin k) :
    survivalMass p j = (p j).toReal + p.toMeasure.real {t | j < t} := by
  have hs : {t : Fin k | j ≤ t} = {j} ∪ {t | j < t} := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    exact le_iff_eq_or_lt.trans (or_congr eq_comm Iff.rfl)
  rw [survivalMass, hs, measureReal_union (by simp) (Set.toFinite _).measurableSet,
    measureReal_singleton]

/-- `1 - h(j) = P(T > j) / P(T ≥ j)` when `P(T ≥ j) ≠ 0`. -/
theorem one_sub_hazard (p : PMF (Fin k)) {j : Fin k} (hj : survivalMass p j ≠ 0) :
    1 - hazard p j = p.toMeasure.real {t | j < t} / survivalMass p j := by
  rw [hazard, eq_div_iff hj, sub_mul, div_mul_cancel₀ _ hj, one_mul, survivalMass_eq_add]
  ring

/-- The induction behind `prod_one_sub_hazard`, on the value of the grid index. -/
private lemma prod_one_sub_hazard_aux (p : PMF (Fin k)) :
    ∀ (v : ℕ) (m : Fin k), (m : ℕ) = v → survivalMass p m ≠ 0 →
      ∏ j with j ≤ m, (1 - hazard p j) = p.toMeasure.real {t | m < t} := by
  intro v
  induction v with
  | zero =>
    intro m hm hS
    have hfilter : ({j | j ≤ m} : Finset (Fin k)) = {m} := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun h => Fin.ext (by have := Fin.le_iff_val_le_val.1 h; omega), fun h => h.le⟩
    have huniv : survivalMass p m = 1 := by
      have hs : {t : Fin k | m ≤ t} = Set.univ :=
        Set.eq_univ_of_forall fun t => Fin.le_iff_val_le_val.2 (by omega)
      rw [survivalMass, hs, probReal_univ]
    rw [hfilter, prod_singleton, one_sub_hazard p hS, huniv, div_one]
  | succ v ih =>
    intro m hm hS
    set m' : Fin k := ⟨v, by omega⟩ with hm'
    have hlt : m' < m := Fin.lt_def.2 (by simp [hm', hm])
    have htail : {t : Fin k | m' < t} = {t | m ≤ t} := by
      ext t
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.le_iff_val_le_val, hm', hm]
      omega
    have hS' : survivalMass p m' ≠ 0 := by
      rw [survivalMass_eq_add, htail, ← survivalMass]
      have h0 : 0 ≤ survivalMass p m := measureReal_nonneg
      have h1 : 0 ≤ (p m').toReal := ENNReal.toReal_nonneg
      have h2 : 0 < survivalMass p m := lt_of_le_of_ne h0 (Ne.symm hS)
      linarith
    have hfilter : ({j | j ≤ m} : Finset (Fin k)) = insert m ({j | j ≤ m'} : Finset (Fin k)) := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.le_iff_val_le_val,
        Fin.ext_iff, hm', hm]
      omega
    have hnot : m ∉ ({j | j ≤ m'} : Finset (Fin k)) := by simpa using hlt
    rw [hfilter, prod_insert hnot, ih m' rfl hS', htail, ← survivalMass, one_sub_hazard p hS,
      div_mul_cancel₀ _ hS]

/-- **Discrete product-limit identity**: for a law `p` of `T` on the grid and an index `m` with
`P(T ≥ m) ≠ 0`, `∏_{j ≤ m} (1 - h(j)) = P(T > m)`, where `h(j) = P(T = j) / P(T ≥ j)`.
The factors telescope, `1 - h(j) = P(T > j) / P(T ≥ j)` and `P(T ≥ j + 1) = P(T > j)`, starting
from `P(T ≥ 0) = 1`. -/
theorem prod_one_sub_hazard (p : PMF (Fin k)) (m : Fin k) (hm : survivalMass p m ≠ 0) :
    ∏ j with j ≤ m, (1 - hazard p j) = p.toMeasure.real {t | m < t} :=
  prod_one_sub_hazard_aux p m m rfl hm

end ProductLimit

/-! ### Consistency of Kaplan–Meier -/

section KaplanMeier

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℕ → Ω → Fin k × Fin k}

/-- The observed at-risk mass is antitone in the grid index. -/
theorem obsAtRiskMass_antitone (μ : Measure (Fin k × Fin k)) [IsFiniteMeasure μ] :
    Antitone (obsAtRiskMass μ) := fun i j hij =>
  measureReal_mono fun _ hz => le_trans hij hz

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- The Kaplan–Meier estimate of `empiricalData` at grid time `m` is the product of the factors
over grid indices `j ≤ m`. -/
theorem kmSurvival_empiricalData (n : ℕ) (ω : Ω) (m : Fin k) :
    (empiricalData Z n ω).kmSurvival ((m : ℕ) : ℝ) =
      ∏ j with j ≤ m, (empiricalData Z n ω).kmFactor j := by
  rw [CensoredData.kmSurvival]
  refine prod_congr ?_ fun _ _ => rfl
  ext j
  simp only [mem_filter, mem_univ, true_and]
  exact gridTime_le_gridTime_iff

/-- A nonzero at-risk mass at `m` gives a nonzero at-risk mass at every `j ≤ m`. -/
theorem obsAtRiskMass_ne_zero_of_le (μ : Measure (Fin k × Fin k)) [IsFiniteMeasure μ]
    {j m : Fin k} (hjm : j ≤ m) (hm : obsAtRiskMass μ m ≠ 0) : obsAtRiskMass μ j ≠ 0 :=
  (lt_of_lt_of_le (lt_of_le_of_ne measureReal_nonneg (Ne.symm hm))
    (obsAtRiskMass_antitone μ hjm)).ne'

/-- **Convergence of the Kaplan–Meier factors**: under independent censoring, almost surely,
simultaneously for every grid index `j` with `P(min T C ≥ j) ≠ 0`, the factor `1 - dⱼ / nⱼ`
converges to `1 - h(j)`, where `h` is the hazard of `T`. -/
theorem ae_tendsto_kmFactor (pT pC : PMF (Fin k)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) (indepLaw pT pC) P) :
    ∀ᵐ ω ∂P, ∀ j, obsAtRiskMass (indepLaw pT pC) j ≠ 0 →
      Tendsto (fun n : ℕ => (empiricalData Z n ω).kmFactor j) atTop (𝓝 (1 - hazard pT j)) := by
  have hR := ae_all_iff.2 (ae_tendsto_atRisk_div hind hlaw)
  have hD := ae_all_iff.2 (ae_tendsto_deaths_div hind hlaw)
  filter_upwards [hR, hD] with ω hRω hDω j hne
  rw [← obsEventMass_div_obsAtRiskMass pT pC j hne]
  refine (tendsto_const_nhds.sub ((hDω j).div (hRω j) hne)).congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  simp only [Pi.div_apply]
  rw [CensoredData.kmFactor, div_div_div_cancel_right₀ (Nat.cast_ne_zero.2 hn)]

/-- **Consistency of the Kaplan–Meier estimator at a grid time.** Let the subjects
`Zᵢ = (Tᵢ, Cᵢ)` be independent with the independent censoring law `indepLaw pT pC` (the product
of the law `pT` of `T` and the law `pC` of `C`). If the observed at-risk mass `P(min T C ≥ m)`
is nonzero, then almost surely the Kaplan–Meier estimate at time `m` converges to
`∏_{j ≤ m} (1 - h(j))`, where `h` is the hazard of `T`; by `prod_one_sub_hazard` this is
`P(T > m)` (`ae_tendsto_kmSurvival_survival`). This is consistency for the survival function of
`T` at grid points only. -/
theorem ae_tendsto_kmSurvival (pT pC : PMF (Fin k)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) (indepLaw pT pC) P) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (empiricalData Z n ω).kmSurvival ((m : ℕ) : ℝ)) atTop
      (𝓝 (∏ j with j ≤ m, (1 - hazard pT j))) := by
  filter_upwards [ae_tendsto_kmFactor pT pC hind hlaw] with ω hω
  simp_rw [kmSurvival_empiricalData]
  exact tendsto_finsetProd _ fun j hj =>
    hω j (obsAtRiskMass_ne_zero_of_le _ (by simpa using hj) hm)

/-- **Consistency of the Kaplan–Meier estimator at a grid time, survival form**: under the
hypotheses of `ae_tendsto_kmSurvival`, almost surely the Kaplan–Meier estimate at time `m`
converges to `P(T > m)`. -/
theorem ae_tendsto_kmSurvival_survival (pT pC : PMF (Fin k)) (hind : iIndepFun Z P)
    (hlaw : ∀ i, HasLaw (Z i) (indepLaw pT pC) P) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (empiricalData Z n ω).kmSurvival ((m : ℕ) : ℝ)) atTop
      (𝓝 (pT.toMeasure.real {t | m < t})) := by
  rw [← prod_one_sub_hazard pT m ((obsAtRiskMass_indepLaw_ne_zero_iff pT pC m).1 hm).1]
  exact ae_tendsto_kmSurvival pT pC hind hlaw m hm

/-- **Consistency of Kaplan–Meier on the canonical sequence space**: on `ℕ → Fin k × Fin k` with
the product measure `Measure.infinitePi (fun _ => indepLaw pT pC)` and coordinate subjects
`Zᵢ ω = ω i`, if `P(min T C ≥ m) ≠ 0` then almost surely the Kaplan–Meier estimate at time `m`
converges to `P(T > m)`. -/
theorem ae_tendsto_kmSurvival_infinitePi (pT pC : PMF (Fin k)) (m : Fin k)
    (hm : obsAtRiskMass (indepLaw pT pC) m ≠ 0) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => indepLaw pT pC),
      Tendsto (fun n : ℕ => (empiricalData (fun i ω => ω i) n ω).kmSurvival ((m : ℕ) : ℝ))
        atTop (𝓝 (pT.toMeasure.real {t | m < t})) :=
  ae_tendsto_kmSurvival_survival pT pC
    (iIndepFun_infinitePi (X := fun _ => id) fun _ => measurable_id)
    (fun i => (measurePreserving_eval_infinitePi (fun _ : ℕ => indepLaw pT pC) i).hasLaw) m hm

end KaplanMeier

end MathlibExt.Probability.Statistics.SurvivalConsistency
