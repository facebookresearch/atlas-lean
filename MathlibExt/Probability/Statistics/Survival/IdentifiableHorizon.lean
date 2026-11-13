/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KaplanMeier
public import MathlibExt.Probability.Statistics.Survival.Censoring
public import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Real

/-!
# The identifiable time horizon of right-censored data

Right censoring hides the event-time law beyond the last time at which subjects can still be
observed. This file makes that precise at two levels.

**Sample level (the Kaplan–Meier NPMLE).** For grouped data `D : CensoredData k` with every
observation time at most `s` (the *horizon*, e.g. the largest observation time), the censored-data
likelihood of a probability measure depends only on its restriction to `(-∞, s]`. The
Kaplan–Meier measure `D.kmMeasure τ` places its residual mass `D.kmTail` at an arbitrary point
`τ > s`; the location `τ` is not determined by the data:

* `likelihood_eq_of_restrict_Iic_eq`: probability measures that agree on `(-∞, s]` have the same
  likelihood.
* `likelihood_le_of_restrict_Iic_eq_kmMeasure`: every probability measure that agrees with the
  Kaplan–Meier measure on `(-∞, s]`, whatever it does on `(s, ∞)`, is an NPMLE.
* `kmMeasure_restrict_Iic_eq`: the Kaplan–Meier measures for two residual locations `τ, τ' > s`
  agree on `(-∞, s]`.
* `kmMeasure_ne_of_kmTail_ne_zero`, `kmTail_pos_of_censored_pos`: when the residual mass is
  nonzero (for instance when a subject is censored at the largest observation time), different
  locations give different measures.
* `kmMeasure_tail_not_identified`: the combined statement: two different maximizers of the
  likelihood that agree up to the horizon.
* `kmMeasure_eq_of_kmTail_eq_zero`: conversely, without residual mass the location is irrelevant.

**Population level (the observed-data law).** In the grid model of `Censoring`, with event time
`T` and censoring time `C` on `Fin k`, one observes `(min T C, 1[T ≤ C])` (`censoredObsMap`),
whose law is `censoredObsLaw μ`. Call `h` a *censoring horizon* of `pC` (`IsCensoringHorizon`)
if it is the largest point of the support of `pC`. In the independent model `indepLaw pT pC`:

* `censoredObsLaw_indepLaw_eq_of_eqOn_Iic`: two event-time laws that agree at every `t ≤ h` give
  the same observed-data law, however they distribute the mass `P(T > h)` beyond the horizon.
* `eqOn_Iic_of_censoredObsLaw_indepLaw_eq`: conversely the observed-data law determines
  `P(T = t)` at every `t ≤ h`.
* `censoredObsLaw_indepLaw_eq_iff`: the two together: the identifiable part of the event-time
  law is exactly its restriction to `{t ≤ h}`.

`obsEventMass_eq_censoredObsLaw` and `obsAtRiskMass_eq_censoredObsLaw` record that the observed
masses of `Censoring` (the inputs of the Kaplan–Meier consistency theorem in `Consistency`) are
functions of `censoredObsLaw`.

## Scope

The population statement is for the finite grid and the independent censoring model of
`Censoring`. It is a statement about one subject's observed-data law; for i.i.d. subjects the
grouped data `SurvivalConsistency.empiricalData` is a function of the observations, so equality of
the single-subject laws transfers to the sample, but that transfer is not formalized here.

## References

* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Sections 1.2 and 3.2.
* E. L. Kaplan and P. Meier, *Nonparametric estimation from incomplete observations*, J. Amer.
  Statist. Assoc. 53 (1958), 457–481.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Finset

namespace MathlibExt.Probability.Statistics.KaplanMeier

namespace CensoredData

variable {k : ℕ} (D : CensoredData k)

/-- The mass of a set at or before the horizon is determined by the restriction to `(-∞, s]`. -/
private lemma measureReal_eq_of_restrict_Iic_eq {μ ν : Measure ℝ} {s : ℝ}
    (h : μ.restrict (Set.Iic s) = ν.restrict (Set.Iic s)) {B : Set ℝ} (hB : MeasurableSet B)
    (hBs : B ⊆ Set.Iic s) : μ.real B = ν.real B := by
  have := congrArg (fun m : Measure ℝ => m.real B) h
  simpa [measureReal_restrict_apply hB, Set.inter_eq_left.2 hBs] using this

/-- **The likelihood only sees the law up to the horizon**: if every observation time is at most
`s`, two probability measures that agree on `(-∞, s]` have the same censored-data likelihood. -/
theorem likelihood_eq_of_restrict_Iic_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {s : ℝ} (hs : ∀ j, D.time j ≤ s)
    (h : μ.restrict (Set.Iic s) = ν.restrict (Set.Iic s)) :
    D.likelihood μ = D.likelihood ν := by
  have hatom : ∀ j, μ.real {D.time j} = ν.real {D.time j} := fun j =>
    measureReal_eq_of_restrict_Iic_eq h (measurableSet_singleton _)
      (Set.singleton_subset_iff.2 (hs j))
  have htail : ∀ j, μ.real (Set.Ioi (D.time j)) = ν.real (Set.Ioi (D.time j)) := fun j => by
    rw [← Set.compl_Iic, measureReal_compl measurableSet_Iic, measureReal_compl measurableSet_Iic,
      measureReal_eq_of_restrict_Iic_eq h measurableSet_Iic (Set.Iic_subset_Iic.2 (hs j)),
      probReal_univ, probReal_univ]
  simp only [likelihood, hatom, htail]

/-- **Any extension of the Kaplan–Meier measure beyond the horizon is an NPMLE**: if every
observation time is at most `s < τ` and a probability measure `μ` agrees with `D.kmMeasure τ` on
`(-∞, s]`, then every probability measure has likelihood at most that of `μ`, whatever `μ` does
on `(s, ∞)`. -/
theorem likelihood_le_of_restrict_Iic_eq_kmMeasure {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {s τ : ℝ} (hs : ∀ j, D.time j ≤ s) (hsτ : s < τ)
    (h : μ.restrict (Set.Iic s) = (D.kmMeasure τ).restrict (Set.Iic s))
    (ν : Measure ℝ) [IsProbabilityMeasure ν] : D.likelihood ν ≤ D.likelihood μ := by
  have := D.kmMeasure_isProbabilityMeasure τ
  rw [D.likelihood_eq_of_restrict_Iic_eq hs h]
  exact D.likelihood_le_kmMeasure ν fun j => (hs j).trans_lt hsτ

/-- **The residual location does not change the law up to the horizon**: for `τ, τ' > s`, the
Kaplan–Meier measures `D.kmMeasure τ` and `D.kmMeasure τ'` agree on `(-∞, s]`. -/
theorem kmMeasure_restrict_Iic_eq {s τ τ' : ℝ} (hsτ : s < τ) (hsτ' : s < τ') :
    (D.kmMeasure τ).restrict (Set.Iic s) = (D.kmMeasure τ').restrict (Set.Iic s) := by
  classical
  have := D.kmMeasure_isProbabilityMeasure τ
  have := D.kmMeasure_isProbabilityMeasure τ'
  ext B hB
  rw [Measure.restrict_apply hB, Measure.restrict_apply hB]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  rw [← measureReal_def, ← measureReal_def, D.kmMeasure_real_apply τ (hB.inter measurableSet_Iic),
    D.kmMeasure_real_apply τ' (hB.inter measurableSet_Iic)]
  have h1 : τ ∉ B ∩ Set.Iic s := fun h => (not_le.2 hsτ) h.2
  have h2 : τ' ∉ B ∩ Set.Iic s := fun h => (not_le.2 hsτ') h.2
  simp [h1, h2]

/-- Without residual Kaplan–Meier mass, the residual location is irrelevant. -/
theorem kmMeasure_eq_of_kmTail_eq_zero (h : D.kmTail = 0) (τ τ' : ℝ) :
    D.kmMeasure τ = D.kmMeasure τ' := by
  simp [kmMeasure, h]

/-- **Different residual locations give different measures** when the residual mass is nonzero
and both locations lie after every observation time. -/
theorem kmMeasure_ne_of_kmTail_ne_zero (h : D.kmTail ≠ 0) {τ τ' : ℝ} (hτ : ∀ j, D.time j < τ)
    (hne : τ ≠ τ') : D.kmMeasure τ ≠ D.kmMeasure τ' := by
  classical
  intro heq
  have h1 := D.kmMeasure_real_apply τ (measurableSet_singleton τ)
  have h2 := D.kmMeasure_real_apply τ' (measurableSet_singleton τ)
  rw [heq] at h1
  have hne' : τ' ∉ ({τ} : Set ℝ) := fun h => hne (Set.mem_singleton_iff.1 h).symm
  have htime : ∀ j, D.time j ∉ ({τ} : Set ℝ) := fun j h =>
    (hτ j).ne (Set.mem_singleton_iff.1 h)
  simp only [htime, hne', Set.mem_singleton_iff, ite_false, ite_true, sum_const_zero,
    zero_add] at h1 h2
  exact h (h1.symm.trans h2)

/-- At or after the last observation time the Kaplan–Meier estimate is the residual mass. -/
theorem kmSurvival_eq_kmTail {t : ℝ} (ht : ∀ j, D.time j ≤ t) : D.kmSurvival t = D.kmTail := by
  classical
  rw [kmSurvival, kmTail, filter_true_of_mem fun j _ => ht j]

/-- **A subject censored at the last observation time leaves residual mass**: the Kaplan–Meier
residual mass is positive. -/
theorem kmTail_pos_of_censored_pos {j : Fin k} (hj : ∀ l, D.time l ≤ D.time j)
    (hc : 0 < D.censored j) : 0 < D.kmTail :=
  D.kmSurvival_eq_kmTail hj ▸ D.kmSurvival_pos_of_censored_pos hc

/-- **The residual location of the NPMLE does not identify the tail.** If every observation time
is at most the horizon `s` and the residual Kaplan–Meier mass is nonzero, then for any two
distinct locations `τ, τ' > s` the Kaplan–Meier measures are different, agree on `(-∞, s]`, have
the same likelihood, and both maximize the likelihood over all probability measures. -/
theorem kmMeasure_tail_not_identified {s τ τ' : ℝ} (hs : ∀ j, D.time j ≤ s)
    (htail : D.kmTail ≠ 0) (hsτ : s < τ) (hsτ' : s < τ') (hne : τ ≠ τ') :
    D.kmMeasure τ ≠ D.kmMeasure τ' ∧
      (D.kmMeasure τ).restrict (Set.Iic s) = (D.kmMeasure τ').restrict (Set.Iic s) ∧
      D.likelihood (D.kmMeasure τ) = D.likelihood (D.kmMeasure τ') ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν →
        D.likelihood ν ≤ D.likelihood (D.kmMeasure τ) ∧
          D.likelihood ν ≤ D.likelihood (D.kmMeasure τ') := by
  have := D.kmMeasure_isProbabilityMeasure τ
  have := D.kmMeasure_isProbabilityMeasure τ'
  have hres := D.kmMeasure_restrict_Iic_eq hsτ hsτ'
  refine ⟨D.kmMeasure_ne_of_kmTail_ne_zero htail (fun j => (hs j).trans_lt hsτ) hne, hres,
    D.likelihood_eq_of_restrict_Iic_eq hs hres, fun ν _ => ⟨?_, ?_⟩⟩
  · exact D.likelihood_le_kmMeasure ν fun j => (hs j).trans_lt hsτ
  · exact D.likelihood_le_kmMeasure ν fun j => (hs j).trans_lt hsτ'

end CensoredData

end MathlibExt.Probability.Statistics.KaplanMeier

namespace MathlibExt.Probability.Statistics.Censoring

variable {k : ℕ}

/-- The **observation map** of right-censored data on the grid: from the event and censoring times
`(T, C)` one observes the follow-up index `min T C` and the event flag `1[T ≤ C]` (ties count as
events, as in `obsEventMass`). -/
def censoredObsMap (ω : Fin k × Fin k) : Fin k × Bool := (min ω.1 ω.2, decide (ω.1 ≤ ω.2))

/-- The **observed-data law** of right-censored data: the law of `censoredObsMap (T, C)` when
`(T, C)` has joint law `μ`. -/
noncomputable def censoredObsLaw (μ : Measure (Fin k × Fin k)) : Measure (Fin k × Bool) :=
  μ.map censoredObsMap

/-- `h` is the **censoring horizon** of the censoring law `pC`: the largest point of its support,
i.e. `P(C = h) ≠ 0` and `P(C = c) = 0` for every `c > h`. -/
def IsCensoringHorizon (pC : PMF (Fin k)) (h : Fin k) : Prop :=
  pC h ≠ 0 ∧ ∀ c, h < c → pC c = 0

/-- The censoring horizon is unique. -/
theorem IsCensoringHorizon.unique {pC : PMF (Fin k)} {h h' : Fin k} (hh : IsCensoringHorizon pC h)
    (hh' : IsCensoringHorizon pC h') : h = h' := by
  rcases lt_trichotomy h h' with hlt | heq | hlt
  · exact absurd (hh.2 h' hlt) hh'.1
  · exact heq
  · exact absurd (hh'.2 h hlt) hh.1

/-- The observation map is measurable (its domain is finite and discrete). -/
theorem measurable_censoredObsMap : Measurable (censoredObsMap (k := k)) :=
  measurable_of_countable _

/-- The mass of a set of observations is the mass of its preimage. -/
theorem censoredObsLaw_apply (μ : Measure (Fin k × Fin k)) (s : Set (Fin k × Bool)) :
    censoredObsLaw μ s = μ (censoredObsMap ⁻¹' s) :=
  Measure.map_apply measurable_censoredObsMap (Set.toFinite s).measurableSet

/-- An observed event at `j` means `T = j ≤ C`. -/
theorem censoredObsMap_preimage_true (j : Fin k) :
    censoredObsMap ⁻¹' {(j, true)} = ({j} : Set (Fin k)) ×ˢ {c | j ≤ c} := by
  ext ⟨t, c⟩
  rw [← obsEvent_set_eq]
  simp [censoredObsMap, Prod.ext_iff]

/-- An observed censoring at `j` means `C = j < T`. -/
theorem censoredObsMap_preimage_false (j : Fin k) :
    censoredObsMap ⁻¹' {(j, false)} = {t | j < t} ×ˢ ({j} : Set (Fin k)) := by
  ext ⟨t, c⟩
  simp only [censoredObsMap, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
    decide_eq_false_iff_not, not_le, Set.mem_prod, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    rw [min_eq_right h2.le] at h1
    subst h1
    exact ⟨h2, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact ⟨min_eq_right h1.le, h1⟩

/-- The observed event mass of `Censoring` is a mass of the observed-data law. -/
theorem obsEventMass_eq_censoredObsLaw (μ : Measure (Fin k × Fin k)) (j : Fin k) :
    obsEventMass μ j = (censoredObsLaw μ).real {(j, true)} := by
  rw [obsEventMass, measureReal_def, measureReal_def, censoredObsLaw_apply,
    censoredObsMap_preimage_true,
    obsEvent_set_eq]

/-- The observed at-risk mass of `Censoring` is a mass of the observed-data law. -/
theorem obsAtRiskMass_eq_censoredObsLaw (μ : Measure (Fin k × Fin k)) (j : Fin k) :
    obsAtRiskMass μ j = (censoredObsLaw μ).real {x | j ≤ x.1} := by
  rw [obsAtRiskMass, measureReal_def, measureReal_def, censoredObsLaw_apply]
  rfl

/-- Observed events under independent censoring: `P(X = j, δ = 1) = P(T = j) P(C ≥ j)`. -/
theorem censoredObsLaw_indepLaw_true (pT pC : PMF (Fin k)) (j : Fin k) :
    censoredObsLaw (indepLaw pT pC) {(j, true)} = pT j * pC.toMeasure {c | j ≤ c} := by
  rw [censoredObsLaw_apply, censoredObsMap_preimage_true, indepLaw, Measure.prod_prod,
    pT.toMeasure_apply_singleton j (measurableSet_singleton j)]

/-- Observed censorings under independent censoring: `P(X = j, δ = 0) = P(T > j) P(C = j)`. -/
theorem censoredObsLaw_indepLaw_false (pT pC : PMF (Fin k)) (j : Fin k) :
    censoredObsLaw (indepLaw pT pC) {(j, false)} = pT.toMeasure {t | j < t} * pC j := by
  rw [censoredObsLaw_apply, censoredObsMap_preimage_false, indepLaw, Measure.prod_prod,
    pC.toMeasure_apply_singleton j (measurableSet_singleton j)]

/-- Beyond the censoring horizon nobody is under observation: `P(C ≥ j) = 0` for `j > h`. -/
private lemma toMeasure_Ici_eq_zero {pC : PMF (Fin k)} {h j : Fin k}
    (hC : ∀ c, h < c → pC c = 0) (hj : h < j) : pC.toMeasure {c | j ≤ c} = 0 := by
  have hs : {c : Fin k | j ≤ c} = ↑(univ.filter (j ≤ ·)) := by ext; simp
  rw [hs, PMF.toMeasure_apply_finset]
  exact sum_eq_zero fun c hc => hC c (hj.trans_le (mem_filter.1 hc).2)

/-- **The tail beyond the censoring horizon is not identified.** If the censoring law puts no
mass after `h`, two event-time laws that agree at every `t ≤ h` have the same observed-data law
under independent censoring, however they distribute `P(T > h)` over the points after `h`. -/
theorem censoredObsLaw_indepLaw_eq_of_eqOn_Iic {pT pT' pC : PMF (Fin k)} {h : Fin k}
    (hC : ∀ c, h < c → pC c = 0) (hT : ∀ t ≤ h, pT t = pT' t) :
    censoredObsLaw (indepLaw pT pC) = censoredObsLaw (indepLaw pT' pC) := by
  refine Measure.ext_of_singleton fun ⟨j, b⟩ => ?_
  cases b with
  | true =>
    rw [censoredObsLaw_indepLaw_true, censoredObsLaw_indepLaw_true]
    rcases le_or_gt j h with hj | hj
    · rw [hT j hj]
    · rw [toMeasure_Ici_eq_zero hC hj, mul_zero, mul_zero]
  | false =>
    rw [censoredObsLaw_indepLaw_false, censoredObsLaw_indepLaw_false]
    rcases le_or_gt j h with hj | hj
    · have hs : {t : Fin k | j < t} = (↑(univ.filter (· ≤ j)) : Set (Fin k))ᶜ := by
        ext; simp
      rw [hs, prob_compl_eq_one_sub (Finset.measurableSet _),
        prob_compl_eq_one_sub (Finset.measurableSet _), PMF.toMeasure_apply_finset,
        PMF.toMeasure_apply_finset,
        sum_congr rfl fun t ht => hT t ((mem_filter.1 ht).2.trans hj)]
    · rw [hC j hj, mul_zero, mul_zero]

/-- **Identification up to the censoring horizon.** If `P(C = h) ≠ 0`, the observed-data law
under independent censoring determines `P(T = t)` at every `t ≤ h`. -/
theorem eqOn_Iic_of_censoredObsLaw_indepLaw_eq {pT pT' pC : PMF (Fin k)} {h : Fin k} (hC : pC h ≠ 0)
    (heq : censoredObsLaw (indepLaw pT pC) = censoredObsLaw (indepLaw pT' pC)) :
    ∀ t ≤ h, pT t = pT' t := by
  intro t ht
  have h1 := congrArg (fun m : Measure (Fin k × Bool) => m {(t, true)}) heq
  simp only [censoredObsLaw_indepLaw_true] at h1
  have hpos : pC.toMeasure {c | t ≤ c} ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hC) ?_)
    rw [← pC.toMeasure_apply_singleton h (measurableSet_singleton h)]
    exact measure_mono (Set.singleton_subset_iff.2 ht)
  exact (ENNReal.mul_left_inj hpos (measure_ne_top _ _)).1 h1

/-- **The identifiable horizon.** If `h` is the censoring horizon of `pC`, two event-time laws
give the same observed-data law under independent censoring if and only if they agree at every
`t ≤ h`: the observed data identify the event-time law exactly up to the horizon and nothing
beyond it. -/
theorem censoredObsLaw_indepLaw_eq_iff {pT pT' pC : PMF (Fin k)} {h : Fin k}
    (hh : IsCensoringHorizon pC h) :
    censoredObsLaw (indepLaw pT pC) = censoredObsLaw (indepLaw pT' pC) ↔ ∀ t ≤ h, pT t = pT' t :=
  ⟨eqOn_Iic_of_censoredObsLaw_indepLaw_eq hh.1, censoredObsLaw_indepLaw_eq_of_eqOn_Iic hh.2⟩

end MathlibExt.Probability.Statistics.Censoring
