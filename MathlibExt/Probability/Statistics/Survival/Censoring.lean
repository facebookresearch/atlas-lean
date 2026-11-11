/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Identification of the discrete hazard under independent censoring

Let the event time `T` and the censoring time `C` take values in the finite grid `Fin k`, with
joint law `μ` on `Fin k × Fin k` (`T = Prod.fst`, `C = Prod.snd`). One observes only the
follow-up time `X = min T C` and the event indicator `δ = 1[T ≤ C]`. As in
`MathlibExt.Probability.Statistics.KaplanMeier`, ties count as events: a subject whose censoring
time equals its event time is observed to fail (censoring comes after the events at a tied time).

At grid point `j` the observable quantities are the **event mass** `P(X = j, δ = 1)`
(`obsEventMass`) and the **at-risk mass** `P(X ≥ j)` (`obsAtRiskMass`). The target is the
discrete **hazard** of `T`, `h(j) = P(T = j) / P(T ≥ j)` (`hazard`).

In the canonical independent model `μ = law(T) ⊗ law(C)` (`indepLaw`) both observed masses
factor through the censoring survival `P(C ≥ j)`, which therefore cancels in their ratio.

## Main results

* `obsEventMass_indepLaw`, `obsAtRiskMass_indepLaw`: the factorizations
  `P(X = j, δ = 1) = P(T = j) P(C ≥ j)` and `P(X ≥ j) = P(T ≥ j) P(C ≥ j)`.
* `obsEventMass_div_obsAtRiskMass`: **identification of the hazard**: if `P(C ≥ j) ≠ 0` then
  `P(X = j, δ = 1) / P(X ≥ j) = h(j)`. No positivity of `P(T ≥ j)` is needed, since both sides
  vanish when it is zero.
* `obsEventMass_div_obsAtRiskMass_of_ne_zero`: the same under the hypothesis `P(X ≥ j) ≠ 0`.
* `causeEventMass_div_obsAtRiskMass`: the competing-risks analogue: with a cause `J` and `(T, J)`
  independent of `C`, the observed cause-`c` event ratio is the cause-specific hazard
  `P(T = j, J = c) / P(T ≥ j)`.

Independence matters: `MathlibExtTest.Probability.Statistics.Censoring` exhibits a dependent joint
law on `Fin 3 × Fin 3` for which the observed ratio differs from the hazard of `T`.

## Scope

This is the identification identity on a finite grid only. Consistency of the Kaplan–Meier
estimator and the non-identifiability of the tail beyond the censoring support are not treated.

## References

* J. D. Kalbfleisch and R. L. Prentice, *The Statistical Analysis of Failure Time Data*, 2nd ed.,
  Wiley (2002), Sections 1.2 and 3.2 (discrete hazard; independent censoring).
* A. Tsiatis, *A nonidentifiability aspect of the problem of competing risks*, Proc. Natl. Acad.
  Sci. USA 72 (1975), 20–22.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.Censoring

open MeasureTheory

variable {k : ℕ}

/-- The observed **event mass** at grid point `j` under the joint law `μ` of `(T, C)`:
`P(min T C = j, T ≤ C)`, the probability that follow-up ends at `j` with an observed event. -/
noncomputable def obsEventMass (μ : Measure (Fin k × Fin k)) (j : Fin k) : ℝ :=
  μ.real {ω | min ω.1 ω.2 = j ∧ ω.1 ≤ ω.2}

/-- The observed **at-risk mass** at grid point `j` under the joint law `μ` of `(T, C)`:
`P(min T C ≥ j)`, the probability that a subject is still under observation at `j`. -/
noncomputable def obsAtRiskMass (μ : Measure (Fin k × Fin k)) (j : Fin k) : ℝ :=
  μ.real {ω | j ≤ min ω.1 ω.2}

/-- The **survival mass** `P(T ≥ j)` of a law `p` on the grid, i.e. the left limit `S(j-)` of the
survival function at `j`. -/
noncomputable def survivalMass (p : PMF (Fin k)) (j : Fin k) : ℝ :=
  p.toMeasure.real {t | j ≤ t}

/-- The discrete **hazard** `P(T = j) / P(T ≥ j)` of a law `p` on the grid (zero when
`P(T ≥ j) = 0`, by the convention `x / 0 = 0`). -/
noncomputable def hazard (p : PMF (Fin k)) (j : Fin k) : ℝ :=
  (p j).toReal / survivalMass p j

/-- The canonical **independent censoring model**: the product law of the event time `T` with law
`pT` and the censoring time `C` with law `pC`. -/
noncomputable def indepLaw (pT pC : PMF (Fin k)) : Measure (Fin k × Fin k) :=
  pT.toMeasure.prod pC.toMeasure

instance (pT pC : PMF (Fin k)) : IsProbabilityMeasure (indepLaw pT pC) := by
  unfold indepLaw; infer_instance

/-- The real mass of a singleton under `p.toMeasure` is the real value of the point mass. -/
theorem measureReal_singleton {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (p : PMF α) (a : α) : p.toMeasure.real {a} = (p a).toReal := by
  rw [measureReal_def, p.toMeasure_apply_singleton a (measurableSet_singleton a)]

/-- The survival mass as a finite sum of point masses. -/
theorem survivalMass_eq_sum (p : PMF (Fin k)) (j : Fin k) :
    survivalMass p j = ∑ t ∈ Finset.univ.filter (j ≤ ·), (p t).toReal := by
  have hs : {t : Fin k | j ≤ t} = ↑(Finset.univ.filter (j ≤ ·)) := by ext; simp
  rw [survivalMass, measureReal_def, hs, PMF.toMeasure_apply_finset,
    ENNReal.toReal_sum fun t _ => p.apply_ne_top t]

/-- The observed-event set is the rectangle `{T = j} ×ˢ {C ≥ j}`. -/
theorem obsEvent_set_eq (j : Fin k) :
    {ω : Fin k × Fin k | min ω.1 ω.2 = j ∧ ω.1 ≤ ω.2} = {j} ×ˢ {c | j ≤ c} := by
  ext ⟨t, c⟩
  simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hle⟩
    rw [min_eq_left hle] at h
    subst h
    exact ⟨rfl, hle⟩
  · rintro ⟨rfl, h⟩
    exact ⟨min_eq_left h, h⟩

/-- The at-risk set is the rectangle `{T ≥ j} ×ˢ {C ≥ j}`. -/
theorem obsAtRisk_set_eq (j : Fin k) :
    {ω : Fin k × Fin k | j ≤ min ω.1 ω.2} = {t | j ≤ t} ×ˢ {c | j ≤ c} := by
  ext ⟨t, c⟩
  simp

/-- **Factorization of the event mass** under independent censoring:
`P(min T C = j, T ≤ C) = P(T = j) P(C ≥ j)`. -/
theorem obsEventMass_indepLaw (pT pC : PMF (Fin k)) (j : Fin k) :
    obsEventMass (indepLaw pT pC) j = (pT j).toReal * survivalMass pC j := by
  rw [obsEventMass, obsEvent_set_eq, indepLaw, measureReal_prod_prod, measureReal_singleton,
    survivalMass]

/-- **Factorization of the at-risk mass** under independent censoring:
`P(min T C ≥ j) = P(T ≥ j) P(C ≥ j)`. -/
theorem obsAtRiskMass_indepLaw (pT pC : PMF (Fin k)) (j : Fin k) :
    obsAtRiskMass (indepLaw pT pC) j = survivalMass pT j * survivalMass pC j := by
  rw [obsAtRiskMass, obsAtRisk_set_eq, indepLaw, measureReal_prod_prod, survivalMass,
    survivalMass]

/-- Under independent censoring the at-risk mass is nonzero iff both survival masses are. -/
theorem obsAtRiskMass_indepLaw_ne_zero_iff (pT pC : PMF (Fin k)) (j : Fin k) :
    obsAtRiskMass (indepLaw pT pC) j ≠ 0 ↔ survivalMass pT j ≠ 0 ∧ survivalMass pC j ≠ 0 := by
  rw [obsAtRiskMass_indepLaw, mul_ne_zero_iff]

/-- **Identification of the discrete hazard under independent censoring**: if the censoring
survival `P(C ≥ j)` is nonzero, the observed ratio `P(X = j, δ = 1) / P(X ≥ j)` equals the hazard
of `T` at `j`. -/
theorem obsEventMass_div_obsAtRiskMass (pT pC : PMF (Fin k)) (j : Fin k)
    (hC : survivalMass pC j ≠ 0) :
    obsEventMass (indepLaw pT pC) j / obsAtRiskMass (indepLaw pT pC) j = hazard pT j := by
  rw [obsEventMass_indepLaw, obsAtRiskMass_indepLaw, mul_div_mul_right _ _ hC, hazard]

/-- **Identification of the discrete hazard**, stated with the observable hypothesis
`P(X ≥ j) ≠ 0`. -/
theorem obsEventMass_div_obsAtRiskMass_of_ne_zero (pT pC : PMF (Fin k)) (j : Fin k)
    (h : obsAtRiskMass (indepLaw pT pC) j ≠ 0) :
    obsEventMass (indepLaw pT pC) j / obsAtRiskMass (indepLaw pT pC) j = hazard pT j :=
  obsEventMass_div_obsAtRiskMass pT pC j ((obsAtRiskMass_indepLaw_ne_zero_iff pT pC j).1 h).2

/-! ### Competing risks -/

section CompetingRisks

variable {r : ℕ}

/-- The **independent censoring model with competing risks**: the event time and cause `(T, J)`
have joint law `pTJ` on `Fin k × Fin r`, independent of the censoring time `C` with law `pC`. -/
noncomputable def indepCauseLaw (pTJ : PMF (Fin k × Fin r)) (pC : PMF (Fin k)) :
    Measure ((Fin k × Fin r) × Fin k) :=
  pTJ.toMeasure.prod pC.toMeasure

/-- The observed **cause-`c` event mass** at `j` under a joint law `μ` of `((T, J), C)`:
`P(min T C = j, T ≤ C, J = c)`. -/
noncomputable def causeEventMass (μ : Measure ((Fin k × Fin r) × Fin k)) (j : Fin k)
    (c : Fin r) : ℝ :=
  μ.real {ω | min ω.1.1 ω.2 = j ∧ ω.1.1 ≤ ω.2 ∧ ω.1.2 = c}

/-- The observed **at-risk mass** at `j` under a joint law `μ` of `((T, J), C)`:
`P(min T C ≥ j)`. -/
noncomputable def causeAtRiskMass (μ : Measure ((Fin k × Fin r) × Fin k)) (j : Fin k) : ℝ :=
  μ.real {ω | j ≤ min ω.1.1 ω.2}

/-- The **cause-specific hazard** `P(T = j, J = c) / P(T ≥ j)` of a joint law `pTJ` of `(T, J)`. -/
noncomputable def causeHazard (pTJ : PMF (Fin k × Fin r)) (j : Fin k) (c : Fin r) : ℝ :=
  (pTJ (j, c)).toReal / pTJ.toMeasure.real {x | j ≤ x.1}

/-- **Identification of the cause-specific hazard under independent censoring**: if
`P(C ≥ j) ≠ 0`, the observed cause-`c` event ratio equals the cause-specific hazard. -/
theorem causeEventMass_div_obsAtRiskMass (pTJ : PMF (Fin k × Fin r)) (pC : PMF (Fin k))
    (j : Fin k) (c : Fin r) (hC : survivalMass pC j ≠ 0) :
    causeEventMass (indepCauseLaw pTJ pC) j c / causeAtRiskMass (indepCauseLaw pTJ pC) j =
      causeHazard pTJ j c := by
  have hE : {ω : (Fin k × Fin r) × Fin k | min ω.1.1 ω.2 = j ∧ ω.1.1 ≤ ω.2 ∧ ω.1.2 = c} =
      {(j, c)} ×ˢ {t | j ≤ t} := by
    ext ⟨⟨t, d⟩, s⟩
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨h, hle, rfl⟩
      rw [min_eq_left hle] at h
      subst h
      exact ⟨⟨rfl, rfl⟩, hle⟩
    · rintro ⟨⟨rfl, rfl⟩, h⟩
      exact ⟨min_eq_left h, h, rfl⟩
  have hR : {ω : (Fin k × Fin r) × Fin k | j ≤ min ω.1.1 ω.2} =
      {x : Fin k × Fin r | j ≤ x.1} ×ˢ {t | j ≤ t} := by
    ext ⟨⟨t, d⟩, s⟩
    simp
  rw [causeEventMass, causeAtRiskMass, hE, hR, indepCauseLaw, measureReal_prod_prod,
    measureReal_prod_prod, measureReal_singleton, ← survivalMass, mul_div_mul_right _ _ hC,
    causeHazard]

end CompetingRisks

end MathlibExt.Probability.Statistics.Censoring
