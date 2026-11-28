/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Censoring
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Real

/-!
# Identification of the discrete hazard under interval censoring

Under right censoring (`Censoring`, `IdentifiableHorizon`) the event time `T` is seen exactly when
it precedes the censoring time, and the hazard is identified up to the censoring horizon. Under
**interval censoring** `T` is not observed directly: the subject is examined at a random finite set
of inspection times, and each examination only reveals whether the event has already happened.
On the discrete grid this can still pin `T` down exactly, when the cell `(L, R]` below contains a
single grid point (for example, when every grid point is inspected).

## Model

The event time `T` and the inspection times live on the grid `Fin k`. The inspection set `S` is a
random `Finset (Fin k)` with law `pS`, independent of `T` (law `pT`). One observes `S` together
with the inspection times at which the event had occurred,

  `(S, {c ∈ S | T ≤ c})`  (`icObsLaw pT pS`),

which is the same as observing the cell `(L, R]` of the partition cut out by `S` that contains `T`,
with `L = max {c ∈ S | c < T}` and `R = min {c ∈ S | T ≤ c}`. Either set can be empty (`S = ∅`,
every inspection before `T`, or every inspection at or after `T`), so the endpoints are extended:
`L = -∞` when no inspection precedes `T` (only `T ≤ R` is learned) and `R = +∞` when the event had
not happened at any inspection (only `L < T` is learned). These are `Finset.max : WithBot (Fin k)`
and `Finset.min : WithTop (Fin k)`, which send `∅` to `⊥` and `⊤`. For `S = ∅` the cell is
`(-∞, +∞)` and nothing is learned about `T`. A single inspection time (`S = {C}`) is *current
status* data (case I interval censoring); two inspection times are case II; a random number of
them is mixed-case interval censoring. Given `S`, the observation has law `inspectLaw pT S`.

## Main results

Let `inspSupport pS` be the set of grid points that are inspected with positive probability
(`c ∈ S` for some `S` with `pS S ≠ 0`), and write `F(c) = P(T ≤ c)`.

* `inspectLaw_eq_iff`: for a fixed inspection set `S`, the law of what is seen is determined by,
  and determines, `F` on `S`. The reverse direction is a π-system argument: the sets `{T ≤ c}`,
  `c ∈ S`, are closed under intersection and generate every event the observation reveals.
* `icObsLaw_eq_iff`: **the identified part of the event-time law**: two event-time laws give the
  same observed-data law iff their distribution functions agree on `inspSupport pS`.
* `hazard_eq_of_icObsLaw_eq`: **identification of the hazard**: the discrete hazard
  `h(j) = P(T = j) / P(T ≥ j)` (`Censoring.hazard`) is identified at `j` when `F(j)` is (`j` is
  inspected, or `j` is the last grid point, where `F = 1`) and `F(j - 1)` is (`j - 1` is inspected,
  or `j = 0`).
* `hazard_identified_iff`: these conditions are also necessary: if `j` (not the last point) or
  `j - 1` is never inspected, two point masses give the same observed-data law and different
  hazards at `j`. At the last grid point the `j - 1` condition is an artifact of the convention
  `x / 0 = 0` in `Censoring.hazard`: there the hazard is `1` whenever `P(T ≥ j) > 0`, and the
  counterexample's hazard `0` comes from `P(T ≥ j) = 0`, so no real information is missing. Away
  from the last point the non-identification is genuine (mix both point masses with the last
  point to make `P(T ≥ j) > 0`).
* `inspSupport_currentStatus`: for current status data the inspected set is the support of the
  inspection-time law, so the hazard at `j` is identified iff both `j` and `j - 1` are possible
  inspection times (up to the boundary cases above).

Contrast with right censoring: there the hazard is identified at every `j` up to the censoring
horizon, whatever the censoring law looks like below it; here it is identified only at grid points
whose two endpoints `j - 1` and `j` are both inspected.

## Scope

Finite grid, independent (noninformative) inspection process, one subject's observed-data law.
Consistency of the nonparametric MLE (Turnbull, Groeneboom–Wellner) is not treated.

## References

* P. Groeneboom and J. A. Wellner, *Information Bounds and Nonparametric Maximum Likelihood
  Estimation*, Birkhäuser (1992), Part II, Section 1.
* B. W. Turnbull, *The empirical distribution function with arbitrarily grouped, censored and
  truncated data*, J. Roy. Statist. Soc. Ser. B 38 (1976), 290–295.
* J. Sun, *The Statistical Analysis of Interval-censored Failure Time Data*, Springer (2006),
  Chapter 1.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.IntervalCensoring

open MeasureTheory Set
open MathlibExt.Probability.Statistics.Censoring (hazard survivalMass measureReal_singleton)

variable {k : ℕ}

/-- The inspection times of `S` at which the event, occurring at `t`, has already happened. -/
def inspect (S : Finset (Fin k)) (t : Fin k) : Finset (Fin k) :=
  S.filter (t ≤ ·)

/-- The law of what is seen at a fixed inspection set `S` when the event time has law `pT`. -/
noncomputable def inspectLaw (pT : PMF (Fin k)) (S : Finset (Fin k)) : PMF (Finset (Fin k)) :=
  pT.map (inspect S)

/-- The **observed-data law under interval censoring**: the law of `(S, inspect S T)` for an
inspection set `S` with law `pS` independent of the event time `T` with law `pT`. -/
noncomputable def icObsLaw (pT : PMF (Fin k)) (pS : PMF (Finset (Fin k))) :
    PMF (Finset (Fin k) × Finset (Fin k)) :=
  pS.bind fun S => (inspectLaw pT S).map (Prod.mk S)

/-- The grid points inspected with positive probability. -/
def inspSupport (pS : PMF (Finset (Fin k))) : Set (Fin k) :=
  {c | ∃ S ∈ pS.support, c ∈ S}

theorem inspect_eq_iff (S A : Finset (Fin k)) (t : Fin k) :
    inspect S t = A ↔ A ⊆ S ∧ ∀ c ∈ S, (t ≤ c ↔ c ∈ A) := by
  constructor
  · rintro rfl
    exact ⟨Finset.filter_subset _ _, fun c hc => by simp [inspect, hc]⟩
  · rintro ⟨hAS, h⟩
    ext c
    simp only [inspect, Finset.mem_filter]
    exact ⟨fun ⟨hc, htc⟩ => (h c hc).1 htc, fun hc => ⟨hAS hc, (h c (hAS hc)).2 hc⟩⟩

theorem inspectLaw_apply (pT : PMF (Fin k)) (S A : Finset (Fin k)) :
    inspectLaw pT S A = pT.toMeasure {t | inspect S t = A} := by
  rw [← PMF.toOuterMeasure_apply_singleton, inspectLaw, PMF.toOuterMeasure_map_apply,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.of_discrete]
  rfl

/-- The event `{inspect S T = A}` lies in the σ-algebra generated by the sets `{T ≤ c}`, `c ∈ S`. -/
theorem measurableSet_inspect_eq (S A : Finset (Fin k)) :
    MeasurableSet[MeasurableSpace.generateFrom {s | ∃ c ∈ S, s = Iic c}]
      {t | inspect S t = A} := by
  have hset : {t : Fin k | inspect S t = A} =
      {_t | A ⊆ S} ∩ ⋂ c ∈ S, {t | t ≤ c ↔ c ∈ A} := by
    ext t
    change inspect S t = A ↔ A ⊆ S ∧ t ∈ ⋂ c ∈ S, {t : Fin k | t ≤ c ↔ c ∈ A}
    rw [mem_iInter₂, inspect_eq_iff]
    rfl
  rw [hset]
  refine (MeasurableSet.const _).inter (Finset.measurableSet_biInter S fun c hc => ?_)
  have hgen : MeasurableSet[MeasurableSpace.generateFrom {s | ∃ c ∈ S, s = Iic c}] (Iic c) :=
    MeasurableSpace.measurableSet_generateFrom ⟨c, hc, rfl⟩
  by_cases hcA : c ∈ A
  · have : {t : Fin k | t ≤ c ↔ c ∈ A} = Iic c := by ext t; simp [hcA]
    rw [this]
    exact hgen
  · have : {t : Fin k | t ≤ c ↔ c ∈ A} = (Iic c)ᶜ := by ext t; simp [hcA]
    rw [this]
    exact hgen.compl

/-- At a fixed inspection set `S`, distribution functions agreeing on `S` give the same law of
what is seen. -/
theorem inspectLaw_eq_of_eqOn {pT pT' : PMF (Fin k)} {S : Finset (Fin k)}
    (h : ∀ c ∈ S, pT.toMeasure (Iic c) = pT'.toMeasure (Iic c)) :
    inspectLaw pT S = inspectLaw pT' S := by
  ext A
  rw [inspectLaw_apply, inspectLaw_apply]
  have hC : IsPiSystem {s : Set (Fin k) | ∃ c ∈ S, s = Iic c} := by
    rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ _
    refine ⟨min c d, ?_, by ext; simp⟩
    rcases min_choice c d with hm | hm <;> rw [hm] <;> assumption
  refine ext_on_measurableSpace_of_generate_finite _ _ ?_
    (MeasurableSpace.generateFrom_le fun _ _ => MeasurableSet.of_discrete) rfl hC
    (by simp only [measure_univ]) (measurableSet_inspect_eq S A)
  rintro _ ⟨c, hc, rfl⟩
  exact h c hc

/-- At a fixed inspection set `S`, the law of what is seen determines `F(c)` at every `c ∈ S`. -/
theorem eqOn_of_inspectLaw_eq {pT pT' : PMF (Fin k)} {S : Finset (Fin k)} {c : Fin k}
    (hc : c ∈ S) (h : inspectLaw pT S = inspectLaw pT' S) :
    pT.toMeasure (Iic c) = pT'.toMeasure (Iic c) := by
  have key : ∀ p : PMF (Fin k),
      p.toMeasure (Iic c) = (inspectLaw p S).toOuterMeasure {A | c ∈ A} := by
    intro p
    rw [inspectLaw, PMF.toOuterMeasure_map_apply,
      PMF.toMeasure_apply_eq_toOuterMeasure_apply _ MeasurableSet.of_discrete]
    congr 1
    ext t
    simp [inspect, hc]
  rw [key, key, h]

/-- For a fixed inspection set `S`, the law of what is seen is exactly as informative as the
distribution function on `S`. -/
theorem inspectLaw_eq_iff {pT pT' : PMF (Fin k)} {S : Finset (Fin k)} :
    inspectLaw pT S = inspectLaw pT' S ↔
      ∀ c ∈ S, pT.toMeasure (Iic c) = pT'.toMeasure (Iic c) :=
  ⟨fun h _ hc => eqOn_of_inspectLaw_eq hc h, inspectLaw_eq_of_eqOn⟩

theorem icObsLaw_apply (pT : PMF (Fin k)) (pS : PMF (Finset (Fin k))) (S A : Finset (Fin k)) :
    icObsLaw pT pS (S, A) = pS S * inspectLaw pT S A := by
  have hmap : ∀ S', (inspectLaw pT S').map (Prod.mk S') (S, A) =
      if S' = S then inspectLaw pT S A else 0 := by
    intro S'
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    split_ifs with hS
    · subst hS
      have : Prod.mk S' ⁻¹' {(S', A)} = {A} := by ext; simp
      rw [this, PMF.toOuterMeasure_apply_singleton]
    · have : Prod.mk S' ⁻¹' {(S, A)} = ∅ := by ext; simp [hS]
      rw [this, measure_empty]
  rw [icObsLaw, PMF.bind_apply, tsum_eq_single S fun S' hS' => by simp [hmap, hS']]
  simp [hmap]

/-- **The identified part of the event-time law under interval censoring.** Two event-time laws
give the same observed-data law iff their distribution functions agree at every grid point that is
inspected with positive probability. -/
theorem icObsLaw_eq_iff {pT pT' : PMF (Fin k)} {pS : PMF (Finset (Fin k))} :
    icObsLaw pT pS = icObsLaw pT' pS ↔
      ∀ c ∈ inspSupport pS, pT.toMeasure (Iic c) = pT'.toMeasure (Iic c) := by
  constructor
  · rintro h c ⟨S, hS, hc⟩
    refine eqOn_of_inspectLaw_eq hc (PMF.ext fun A => ?_)
    have hSA := DFunLike.congr_fun h (S, A)
    rw [icObsLaw_apply, icObsLaw_apply] at hSA
    exact (ENNReal.mul_right_inj hS (PMF.apply_ne_top _ _)).1 hSA
  · intro h
    ext ⟨S, A⟩
    rw [icObsLaw_apply, icObsLaw_apply]
    by_cases hS : pS S = 0
    · rw [hS, zero_mul, zero_mul]
    · rw [inspectLaw_eq_of_eqOn fun c hc => h c ⟨S, hS, hc⟩]

/-! ### The hazard -/

theorem apply_toReal_eq_sub (p : PMF (Fin k)) (j : Fin k) :
    (p j).toReal = p.toMeasure.real (Iic j) - p.toMeasure.real (Iio j) := by
  have hU : Iic j = {j} ∪ Iio j := by
    ext t
    simp [le_iff_lt_or_eq, or_comm]
  rw [hU, measureReal_union (s₁ := {j}) (s₂ := Iio j) (by simp) measurableSet_Iio,
    measureReal_singleton]
  ring

theorem survivalMass_eq_one_sub (p : PMF (Fin k)) (j : Fin k) :
    survivalMass p j = 1 - p.toMeasure.real (Iio j) := by
  have : {t : Fin k | j ≤ t} = (Iio j)ᶜ := by ext; simp
  rw [survivalMass, this, probReal_compl_eq_one_sub measurableSet_Iio]

/-- The hazard at `j` depends on the event-time law only through `F(j)` and `P(T < j)`. -/
theorem hazard_eq_of_eq {pT pT' : PMF (Fin k)} {j : Fin k}
    (hj : pT.toMeasure (Iic j) = pT'.toMeasure (Iic j))
    (hprev : pT.toMeasure (Iio j) = pT'.toMeasure (Iio j)) :
    hazard pT j = hazard pT' j := by
  rw [hazard, hazard, apply_toReal_eq_sub, apply_toReal_eq_sub, survivalMass_eq_one_sub,
    survivalMass_eq_one_sub, measureReal_def, measureReal_def, measureReal_def, measureReal_def,
    hj, hprev]

/-- `P(T < j)` is `F(j - 1)`, or `0` when `j = 0`. -/
theorem toMeasure_Iio_eq {pT pT' : PMF (Fin k)} {j : Fin k}
    (h : ∀ i : Fin k, i.val + 1 = j.val → pT.toMeasure (Iic i) = pT'.toMeasure (Iic i)) :
    pT.toMeasure (Iio j) = pT'.toMeasure (Iio j) := by
  obtain ⟨_ | n, hn⟩ := j
  · have : Iio (⟨0, hn⟩ : Fin k) = ∅ := by
      ext t
      simp [Fin.lt_def]
    rw [this, measure_empty, measure_empty]
  · have : Iio (⟨n + 1, hn⟩ : Fin k) = Iic ⟨n, by omega⟩ := by
      ext t
      simp only [mem_Iio, mem_Iic, Fin.lt_def, Fin.le_def]
      omega
    rw [this]
    exact h _ rfl

theorem toMeasure_Iic_last (p : PMF (Fin k)) {j : Fin k} (hj : j.val + 1 = k) :
    p.toMeasure (Iic j) = 1 := by
  have : Iic j = univ := by
    ext t
    simp only [mem_Iic, mem_univ, iff_true, Fin.le_def]
    omega
  rw [this, measure_univ]

/-- **Identification of the hazard under interval censoring.** If `F(j)` is identified (`j` is
inspected with positive probability, or `j` is the last grid point) and `F(j - 1)` is identified
(`j - 1` is inspected with positive probability, or `j = 0`), then the observed-data law determines
the hazard at `j`. -/
theorem hazard_eq_of_icObsLaw_eq {pT pT' : PMF (Fin k)} {pS : PMF (Finset (Fin k))} {j : Fin k}
    (h : icObsLaw pT pS = icObsLaw pT' pS) (hj : j ∈ inspSupport pS ∨ j.val + 1 = k)
    (hprev : ∀ i : Fin k, i.val + 1 = j.val → i ∈ inspSupport pS) :
    hazard pT j = hazard pT' j := by
  have hF := icObsLaw_eq_iff.1 h
  refine hazard_eq_of_eq ?_ (toMeasure_Iio_eq fun i hi => hF i (hprev i hi))
  rcases hj with hj | hj
  · exact hF j hj
  · rw [toMeasure_Iic_last _ hj, toMeasure_Iic_last _ hj]

/-! ### Sharpness -/

theorem hazard_pure (a j : Fin k) : hazard (PMF.pure a) j = if a = j then 1 else 0 := by
  by_cases h : a = j
  · subst h
    simp [hazard, survivalMass, PMF.toMeasure_pure, measureReal_def, PMF.pure_apply]
  · simp [hazard, PMF.pure_apply, h, Ne.symm h]

/-- Point masses at `a` and `b` give the same observed-data law when their distribution functions
differ only at grid points that are never inspected. -/
theorem icObsLaw_pure_eq {a b : Fin k} {pS : PMF (Finset (Fin k))}
    (h : ∀ c ∈ inspSupport pS, (a ≤ c ↔ b ≤ c)) :
    icObsLaw (PMF.pure a) pS = icObsLaw (PMF.pure b) pS := by
  refine icObsLaw_eq_iff.2 fun c hc => ?_
  rw [PMF.toMeasure_pure, PMF.toMeasure_pure, Measure.dirac_apply, Measure.dirac_apply]
  by_cases ha : a ≤ c
  · rw [indicator_of_mem (mem_Iic.2 ha), indicator_of_mem (mem_Iic.2 ((h c hc).1 ha)),
      Pi.one_apply, Pi.one_apply]
  · rw [indicator_of_notMem (fun h' => ha (mem_Iic.1 h')),
      indicator_of_notMem (fun h' => ha ((h c hc).2 (mem_Iic.1 h')))]

/-- If `j` is never inspected and is not the last grid point, the hazard at `j` is not identified:
point masses at `j` and `j + 1` have the same observed-data law and hazards `1` and `0` at `j`. -/
theorem exists_hazard_ne_of_notMem {pS : PMF (Finset (Fin k))} {j : Fin k}
    (hj : j ∉ inspSupport pS) (hlast : j.val + 1 < k) :
    ∃ pT pT' : PMF (Fin k), icObsLaw pT pS = icObsLaw pT' pS ∧ hazard pT j ≠ hazard pT' j := by
  refine ⟨PMF.pure j, PMF.pure ⟨j.val + 1, hlast⟩, icObsLaw_pure_eq fun c hc => ?_, ?_⟩
  · have hcj : c.val ≠ j.val := fun h' => hj (Fin.ext h' ▸ hc)
    simp only [Fin.le_def]
    omega
  · simp [hazard_pure, Fin.ext_iff]

/-- If `j - 1` is never inspected, the hazard at `j` is not identified: point masses at `j - 1`
and `j` have the same observed-data law and hazards `0` and `1` at `j`. The hazard `0` of the
point mass at `j - 1` is the `x / 0 = 0` convention (`P(T ≥ j) = 0`); see the module docstring. -/
theorem exists_hazard_ne_of_prev_notMem {pS : PMF (Finset (Fin k))} {i j : Fin k}
    (hi : i ∉ inspSupport pS) (hij : i.val + 1 = j.val) :
    ∃ pT pT' : PMF (Fin k), icObsLaw pT pS = icObsLaw pT' pS ∧ hazard pT j ≠ hazard pT' j := by
  refine ⟨PMF.pure i, PMF.pure j, icObsLaw_pure_eq fun c hc => ?_, ?_⟩
  · have hci : c.val ≠ i.val := fun h' => hi (Fin.ext h' ▸ hc)
    simp only [Fin.le_def]
    omega
  · have hne : i ≠ j := fun h' => by rw [h'] at hij; omega
    simp [hazard_pure, hne]

/-- **Characterization of hazard identifiability under interval censoring.** The observed-data
law determines the hazard at `j` for every pair of event-time laws iff `F(j)` and `F(j - 1)` are
identified: `j` is inspected or is the last grid point, and `j - 1` is inspected or `j = 0`. Here
the hazard is `h(j) = P(T = j) / P(T ≥ j)` with `0 / 0 = 0` (`Censoring.hazard`); at the last grid
point the necessity of the `j - 1` condition comes only from that convention (there the hazard is
`1` whenever `P(T ≥ j) > 0`; see the module docstring). -/
theorem hazard_identified_iff {pS : PMF (Finset (Fin k))} {j : Fin k} :
    (∀ pT pT' : PMF (Fin k), icObsLaw pT pS = icObsLaw pT' pS → hazard pT j = hazard pT' j) ↔
      (j ∈ inspSupport pS ∨ j.val + 1 = k) ∧
        ∀ i : Fin k, i.val + 1 = j.val → i ∈ inspSupport pS := by
  constructor
  · intro h
    refine ⟨?_, fun i hij => ?_⟩
    · by_contra hj
      obtain ⟨hj1, hj2⟩ := not_or.1 hj
      obtain ⟨pT, pT', hobs, hne⟩ := exists_hazard_ne_of_notMem hj1 (by omega)
      exact hne (h pT pT' hobs)
    · by_contra hi
      obtain ⟨pT, pT', hobs, hne⟩ := exists_hazard_ne_of_prev_notMem hi hij
      exact hne (h pT pT' hobs)
  · rintro ⟨hj, hprev⟩ pT pT' hobs
    exact hazard_eq_of_icObsLaw_eq hobs hj hprev

/-! ### Current status data -/

/-- **Current status data**: a single inspection time with law `pC`. -/
noncomputable def currentStatus (pC : PMF (Fin k)) : PMF (Finset (Fin k)) :=
  pC.map ({·})

/-- For current status data the inspected grid points are the possible inspection times. -/
theorem inspSupport_currentStatus (pC : PMF (Fin k)) :
    inspSupport (currentStatus pC) = pC.support := by
  ext c
  change (∃ S ∈ (pC.map ({·})).support, c ∈ S) ↔ c ∈ pC.support
  simp only [PMF.support_map, mem_image]
  constructor
  · rintro ⟨_, ⟨c', hc', rfl⟩, hc⟩
    rwa [Finset.mem_singleton.1 hc]
  · intro hc
    exact ⟨{c}, ⟨c, hc, rfl⟩, Finset.mem_singleton_self c⟩

end MathlibExt.Probability.Statistics.IntervalCensoring
