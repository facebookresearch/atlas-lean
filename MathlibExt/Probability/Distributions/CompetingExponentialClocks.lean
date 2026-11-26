/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

import MathlibExt.Probability.Distributions.ExponentialMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Competing exponential clocks -/

open MeasureTheory Set
open scoped ENNReal

namespace ProbabilityTheory

private def raceEvent {Ω : Type*} {n : ℕ} (X : Fin (n + 1) → Ω → ℝ)
    (j : Fin (n + 1)) (t : ℝ) : Set Ω :=
  {ω | t < X j ω ∧ ∀ i, i ≠ j → X j ω < X i ω}

private theorem measurableSet_raceEvent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin (n + 1) → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (j : Fin (n + 1)) (t : ℝ) : MeasurableSet (raceEvent X j t) := by
  have h : raceEvent X j t = (X j ⁻¹' Ioi t) ∩
      ⋂ i : {i : Fin (n + 1) // i ≠ j}, {ω | X j ω < X i ω} := by
    ext ω
    simp [raceEvent]
  rw [h]
  exact (hX j measurableSet_Ioi).inter
    (MeasurableSet.iInter fun i => measurableSet_lt (hX j) (hX i))

private theorem expMeasure_real_Ioi_of_nonneg {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    (expMeasure r).real (Ioi x) = Real.exp (-(r * x)) := by
  let _ := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_expMeasure_eq hr, ite_eq_left hx, sub_sub_cancel]

/-- Split off the first ringing coordinate and integrate over its possible ringing times. -/
private theorem pi_expMeasure_real_raceEvent {n : ℕ} (q : Fin (n + 1) → ℝ)
    (hq : ∀ i, 0 < q i) (j : Fin (n + 1)) {t : ℝ} (ht : 0 ≤ t) :
    (Measure.pi fun i => expMeasure (q i)).real (raceEvent (fun i x => x i) j t) =
      (q j / ∑ i, q i) * Real.exp (-((∑ i, q i) * t)) := by
  classical
  let _ (i : Fin (n + 1)) := isProbabilityMeasure_expMeasure (hq i)
  let Q := ∑ i, q i
  have hQ : 0 < Q := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
  let A : Set (ℝ × (Fin n → ℝ)) := {p | t < p.1 ∧ ∀ i, p.1 < p.2 i}
  have hA : MeasurableSet A := by
    have h : A = (Prod.fst ⁻¹' Ioi t) ∩
        ⋂ i : Fin n, {p : ℝ × (Fin n → ℝ) | p.1 < p.2 i} := by
      ext p
      simp [A]
    rw [h]
    exact (measurable_fst measurableSet_Ioi).inter (MeasurableSet.iInter fun i =>
      measurableSet_lt measurable_fst ((measurable_pi_apply i).comp measurable_snd))
  have he : raceEvent (fun i x => x i) j t = e ⁻¹' A := by
    ext x
    change (t < x j ∧ ∀ i, i ≠ j → x j < x i) ↔
      (t < x j ∧ ∀ i : Fin n, x j < x (j.succAbove i))
    constructor
    · rintro ⟨hx, h⟩
      exact ⟨hx, fun i => h _ (j.succAbove_ne i)⟩
    · rintro ⟨hx, h⟩
      refine ⟨hx, fun i hi => ?_⟩
      obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
      exact h k
  let ν := Measure.pi fun i : Fin n => expMeasure (q (j.succAbove i))
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hpres := measurePreserving_piFinSuccAbove (fun i => expMeasure (q i)) j
  rw [he, measureReal_def, hpres.measure_preimage hA.nullMeasurableSet, Measure.prod_apply hA]
  rw [← integral_toReal (measurable_measure_prodMk_left hA).aemeasurable
    (ae_of_all _ fun x => measure_lt_top ν (Prod.mk x ⁻¹' A))]
  have hsec (x : ℝ) : ν.real (Prod.mk x ⁻¹' A) =
      (Ioi t).indicator (fun x => Real.exp (-((∑ i : Fin n, q (j.succAbove i)) * x))) x := by
    by_cases hx : t < x
    · have hset : Prod.mk x ⁻¹' A = Set.pi univ (fun _ : Fin n => Ioi x) := by
        ext y
        simp [A, hx]
      rw [hset, indicator_of_mem hx]
      simp_rw [ν, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod, ← measureReal_def,
        expMeasure_real_Ioi_of_nonneg (hq _) (ht.trans hx.le)]
      rw [← Real.exp_sum, Finset.sum_neg_distrib, ← Finset.sum_mul]
    · have hset : Prod.mk x ⁻¹' A = ∅ := by ext y; simp [A, hx]
      rw [hset, indicator_of_notMem hx]
      simp
  change (∫ x, ν.real (Prod.mk x ⁻¹' A) ∂expMeasure (q j)) = _
  simp_rw [hsec]
  rw [integral_expMeasure_eq_setIntegral (hq j)]
  have hintegrand : (fun x : ℝ => q j * Real.exp (-(q j * x)) *
      (Ioi t).indicator (fun x => Real.exp (-((∑ i : Fin n, q (j.succAbove i)) * x))) x) =
      (Ioi t).indicator (fun x => q j * Real.exp (-Q * x)) := by
    funext x
    by_cases hx : x ∈ Ioi t
    · simp only [indicator_of_mem hx]
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      rw [show Q = q j + ∑ i : Fin n, q (j.succAbove i) from Fin.sum_univ_succAbove q j]
      ring
    · simp [indicator_of_notMem hx]
  rw [hintegrand, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (fun _ hx => ht.trans_lt hx), integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos hQ)]
  change q j * (-Real.exp (-Q * t) / -Q) = q j / Q * Real.exp (-(Q * t))
  rw [neg_div_neg_eq, neg_mul]
  ring

private theorem real_raceEvent {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (expMeasure (q i)) μ) (hind : iIndepFun X μ)
    (j : Fin (n + 1)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real (raceEvent X j t) = (q j / ∑ i, q i) * Real.exp (-((∑ i, q i) * t)) := by
  let f (ω : Ω) (i : Fin (n + 1)) := X i ω
  have hp : μ.map f = Measure.pi (fun i => expMeasure (q i)) := by
    rw [hind.map_fun_eq_pi_map (fun i => (hX i).aemeasurable)]
    congr 1
    funext i
    exact (hlaw i).map_eq
  have hf : Measurable f := Measurable.of_eval hX
  rw [← pi_expMeasure_real_raceEvent q hq j ht, ← hp,
    map_measureReal_apply hf (measurableSet_raceEvent (fun i => measurable_pi_apply i) j t)]
  rfl

private theorem raceEvent_unique {Ω : Type*} {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    {i j : Fin (n + 1)} {t : ℝ} {ω : Ω} (hi : ω ∈ raceEvent X i t)
    (hj : ω ∈ raceEvent X j t) : i = j := by
  by_contra h
  exact (not_lt_of_ge (hj.2 i h).le) (hi.2 j fun he => h he.symm)

private noncomputable def raceWinner {Ω : Type*} {n : ℕ} (X : Fin (n + 1) → Ω → ℝ)
    (ω : Ω) : Fin (n + 1) := by
  classical
  exact if h : ∃ i, ω ∈ raceEvent X i 0 then h.choose else 0

private theorem raceWinner_mem {Ω : Type*} {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    {ω : Ω} (h : ∃ i, ω ∈ raceEvent X i 0) : ω ∈ raceEvent X (raceWinner X ω) 0 := by
  classical
  simpa only [raceWinner, dite_eq_left h] using h.choose_spec

private theorem measurable_raceWinner {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin (n + 1) → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (raceWinner X) := by
  apply measurable_to_countable
  intro ω
  let j := raceWinner X ω
  change MeasurableSet (raceWinner X ⁻¹' {j})
  classical
  let E := ⋃ i, raceEvent X i 0
  have hE : MeasurableSet E := MeasurableSet.iUnion fun i => measurableSet_raceEvent hX i 0
  have he : raceWinner X ⁻¹' {j} = raceEvent X j 0 ∪ if j = 0 then Eᶜ else ∅ := by
    ext η
    by_cases h : ∃ i, η ∈ raceEvent X i 0
    · have hs := raceWinner_mem h
      have hη : η ∈ E := by simpa only [E, mem_iUnion] using h
      have hnone : η ∉ (if j = 0 then Eᶜ else ∅) := by
        split <;> simp_all
      simp only [mem_preimage, mem_singleton_iff, mem_union, hnone, or_false]
      exact ⟨fun hj => hj ▸ hs, fun hj => raceEvent_unique hs hj⟩
    · have hη : η ∉ E := by simpa only [E, mem_iUnion] using h
      have hnot : η ∉ raceEvent X j 0 := fun hj => h ⟨j, hj⟩
      simp only [mem_preimage, mem_singleton_iff, raceWinner, dite_eq_right h,
        mem_union, hnot, false_or]
      by_cases hj : j = 0
      · simp [hj, hη]
      · simp [hj, show (0 : Fin (n + 1)) ≠ j from fun e => hj e.symm]
  rw [he]
  by_cases hj : j = 0 <;> simp [hj, hE.compl, measurableSet_raceEvent hX]

private noncomputable def raceTime {Ω : Type*} {n : ℕ} (X : Fin (n + 1) → Ω → ℝ)
    (ω : Ω) : ℝ := Finset.univ.inf' Finset.univ_nonempty (fun i => X i ω)

private theorem measurable_raceTime {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {X : Fin (n + 1) → Ω → ℝ} (hX : ∀ i, Measurable (X i)) : Measurable (raceTime X) := by
  apply measurable_of_Ioi
  intro t
  have h : raceTime X ⁻¹' Ioi t = ⋂ i : Fin (n + 1), X i ⁻¹' Ioi t := by
    ext ω
    simp [raceTime, Finset.lt_inf'_iff]
  rw [h]
  exact MeasurableSet.iInter fun i => hX i measurableSet_Ioi

private theorem raceTime_eq_of_mem {Ω : Type*} {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    {j : Fin (n + 1)} {t : ℝ} {ω : Ω} (h : ω ∈ raceEvent X j t) : raceTime X ω = X j ω := by
  apply le_antisymm (Finset.inf'_le _ (Finset.mem_univ j))
  refine Finset.le_inf' _ _ fun i _ => ?_
  by_cases hi : i = j
  · simp [hi]
  · exact (h.2 i hi).le

private theorem raceWinner_spec_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (expMeasure (q i)) μ) (hind : iIndepFun X μ) :
    ∀ᵐ ω ∂μ, ω ∈ raceEvent X (raceWinner X ω) 0 := by
  let E := ⋃ j, raceEvent X j 0
  have hdisj : Pairwise (Function.onFun Disjoint (fun j => raceEvent X j 0)) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun _ hi hj => hij (raceEvent_unique hi hj)
  have hQ : 0 < ∑ i, q i := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  have hE : μ.real E = 1 := by
    rw [measureReal_iUnion_fintype hdisj (fun j => measurableSet_raceEvent hX j 0)]
    simp_rw [real_raceEvent q hq hX hlaw hind _ le_rfl, mul_zero, neg_zero, Real.exp_zero, mul_one]
    rw [← Finset.sum_div, div_self hQ.ne']
  have hnull : μ Eᶜ = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top μ Eᶜ)).mp
    have hEm : MeasurableSet E :=
      MeasurableSet.iUnion fun j => measurableSet_raceEvent hX j 0
    rw [probReal_compl_eq_one_sub hEm, hE, sub_self]
  have hgood : ∀ᵐ ω ∂μ, ω ∈ E := ae_iff.mpr hnull
  filter_upwards [hgood] with ω hω
  exact raceWinner_mem (mem_iUnion.mp hω)

private theorem measureReal_race_slice {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (expMeasure (q i)) μ) (hind : iIndepFun X μ)
    (j : Fin (n + 1)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real (raceTime X ⁻¹' Ioi t ∩ raceWinner X ⁻¹' {j}) =
      (q j / ∑ i, q i) * Real.exp (-((∑ i, q i) * t)) := by
  rw [← real_raceEvent q hq hX hlaw hind j ht]
  apply measureReal_congr
  filter_upwards [raceWinner_spec_ae q hq hX hlaw hind] with ω hω
  have hT := raceTime_eq_of_mem hω
  change (t < raceTime X ω ∧ raceWinner X ω = j) ↔ ω ∈ raceEvent X j t
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨hT ▸ h, hω.2⟩
  · intro h
    have hj := raceEvent_unique hω (show ω ∈ raceEvent X j 0 from ⟨ht.trans_lt h.1, h.2⟩)
    exact ⟨(raceTime_eq_of_mem h).symm ▸ h.1, hj⟩

private theorem race_slice_law {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (expMeasure (q i)) μ) (hind : iIndepFun X μ)
    (j : Fin (n + 1)) :
    (μ.restrict (raceWinner X ⁻¹' {j})).map (raceTime X) =
      ENNReal.ofReal (q j / ∑ i, q i) • expMeasure (∑ i, q i) := by
  let Q := ∑ i, q i
  let w := q j / Q
  have hQ : 0 < Q := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  have hw : 0 ≤ w := div_nonneg (hq j).le hQ.le
  let law := expMeasure Q
  let _ : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure hQ
  let ν := (μ.restrict (raceWinner X ⁻¹' {j})).map (raceTime X)
  let η := ENNReal.ofReal w • law
  have : IsFiniteMeasure η := law.smul_finite ENNReal.ofReal_ne_top
  have hm := measurable_raceTime hX
  have hpos : ∀ᵐ ω ∂μ, 0 < raceTime X ω := by
    filter_upwards [raceWinner_spec_ae q hq hX hlaw hind] with ω hω
    simpa only [raceTime_eq_of_mem hω] using hω.1
  have htail (t : ℝ) (ht : 0 ≤ t) : ν.real (Ioi t) = w * Real.exp (-(Q * t)) := by
    simp only [ν, map_measureReal_apply hm measurableSet_Ioi,
      measureReal_restrict_apply (hm measurableSet_Ioi)]
    exact measureReal_race_slice q hq hX hlaw hind j ht
  have hlow {t : ℝ} (ht : t ≤ 0) : ν.real (Ioi t) = ν.real univ := by
    simp only [ν, map_measureReal_apply hm measurableSet_Ioi,
      map_measureReal_apply hm MeasurableSet.univ,
      measureReal_restrict_apply (hm measurableSet_Ioi), Set.preimage_univ,
      measureReal_restrict_apply_univ]
    apply measureReal_congr
    filter_upwards [hpos] with ω hω
    change (t < raceTime X ω ∧ raceWinner X ω = j) ↔ raceWinner X ω = j
    simp only [ht.trans_lt hω, true_and]
  have hmass : ν.real univ = w := by
    rw [← hlow le_rfl, htail 0 le_rfl, mul_zero, neg_zero, Real.exp_zero, mul_one]
  have hηmass : η.real univ = w := by
    simp [η, ENNReal.toReal_ofReal hw]
  have htails (t : ℝ) : ν.real (Ioi t) = η.real (Ioi t) := by
    by_cases ht : 0 ≤ t
    · rw [htail t ht]
      simp [η, law, ENNReal.toReal_ofReal hw, expMeasure_real_Ioi_of_nonneg hQ ht]
    · have hlawTail : law.real (Ioi t) = 1 := by
        rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real]
        simp [law, cdf_expMeasure_eq hQ, ht]
      rw [hlow (le_of_not_ge ht), hmass]
      simp [η, ENNReal.toReal_ofReal hw, hlawTail]
  change ν = η
  refine Measure.ext_of_Iic ν η (fun t => ?_)
  apply (measureReal_eq_measureReal_iff (measure_ne_top ν _) (measure_ne_top η _)).mp
  have h := htails t
  rw [← compl_Iic, measureReal_compl measurableSet_Iic,
    measureReal_compl measurableSet_Iic, hmass, hηmass] at h
  linarith

private theorem measureReal_race_rectangle {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (expMeasure (q i)) μ) (hind : iIndepFun X μ)
    {s : Set ℝ} (hs : MeasurableSet s) (a : Finset (Fin (n + 1))) :
    μ.real (raceTime X ⁻¹' s ∩ raceWinner X ⁻¹' ↑a) =
      (expMeasure (∑ i, q i)).real s * ∑ j ∈ a, q j / ∑ i, q i := by
  have hQ : 0 < ∑ i, q i := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  have hT := measurable_raceTime hX
  have hJ := measurable_raceWinner hX
  have hfiber (j : Fin (n + 1)) :
      μ.real (raceTime X ⁻¹' s ∩ raceWinner X ⁻¹' {j}) =
        (expMeasure (∑ i, q i)).real s * (q j / ∑ i, q i) := by
    have h := congrArg (fun ν : Measure ℝ => ν.real s) (race_slice_law q hq hX hlaw hind j)
    simpa only [map_measureReal_apply hT hs, measureReal_restrict_apply (hT hs),
      measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal (div_nonneg (hq j).le hQ.le),
      mul_comm] using h
  have ha : MeasurableSet (↑a : Set (Fin (n + 1))) := a.finite_toSet.measurableSet
  calc
    _ = (μ.restrict (raceTime X ⁻¹' s)).real (raceWinner X ⁻¹' ↑a) := by
      rw [measureReal_restrict_apply (hJ ha), inter_comm]
    _ = ∑ j ∈ a, (μ.restrict (raceTime X ⁻¹' s)).real (raceWinner X ⁻¹' {j}) :=
      (sum_measureReal_preimage_singleton a
        (fun j _ => hJ (measurableSet_singleton j))).symm
    _ = _ := by
      simp_rw [measureReal_restrict_apply (hJ (measurableSet_singleton _)),
        inter_comm (raceWinner X ⁻¹' _) (raceTime X ⁻¹' s), hfiber, Finset.mul_sum]

/-- **Competing exponential clocks.** For a nonempty finite family of independent exponential
clocks with positive rates `q i`, let `T` be the minimum and let `Q` be the sum of the rates.
There is a measurable winner `J`, which is the unique minimizer almost surely. The law of `T`
is exponential with rate `Q`, its law is independent of `J`, and the probability of `T > t`
and `J = j` is `(q j / Q) * exp (-(Q * t))` for every `t ≥ 0`. The two-clock case is used in
K. Sigman, *Continuous-Time Markov Chains*, §1.5, for birth and death processes. -/
public theorem competing_exponential_clocks {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {X : Fin (n + 1) → Ω → ℝ}
    (q : Fin (n + 1) → ℝ) (hq : ∀ i, 0 < q i) (hX : ∀ i, Measurable (X i))
    (hlaw : ∀ i, HasLaw (X i) (expMeasure (q i)) μ) (hind : iIndepFun X μ) :
    let T (ω : Ω) := Finset.univ.inf' Finset.univ_nonempty (fun i => X i ω)
    ∃ J : Ω → Fin (n + 1), Measurable J ∧
      (∀ᵐ ω ∂μ, T ω = X (J ω) ω ∧ ∀ i, i ≠ J ω → T ω < X i ω) ∧
      HasLaw T (expMeasure (∑ i, q i)) μ ∧ IndepFun T J μ ∧
      (∀ j, μ.real (J ⁻¹' {j}) = q j / ∑ i, q i) ∧
      ∀ (j : Fin (n + 1)) (t : ℝ), 0 ≤ t →
        μ.real (T ⁻¹' Ioi t ∩ J ⁻¹' {j}) =
          (q j / ∑ i, q i) * Real.exp (-((∑ i, q i) * t)) := by
  classical
  let Q := ∑ i, q i
  have hQ : 0 < Q := Finset.sum_pos (fun i _ => hq i) Finset.univ_nonempty
  let law := expMeasure Q
  let _ : IsProbabilityMeasure law := isProbabilityMeasure_expMeasure hQ
  let J := raceWinner X
  let T := raceTime X
  have hJ : Measurable J := measurable_raceWinner hX
  have hT : Measurable T := measurable_raceTime hX
  have hrect {s : Set ℝ} (hs : MeasurableSet s) (a : Finset (Fin (n + 1))) :
      μ.real (T ⁻¹' s ∩ J ⁻¹' ↑a) = law.real s * ∑ j ∈ a, q j / Q :=
    measureReal_race_rectangle q hq hX hlaw hind hs a
  have hJreal (a : Finset (Fin (n + 1))) :
      μ.real (J ⁻¹' ↑a) = ∑ j ∈ a, q j / Q := by
    simpa only [preimage_univ, univ_inter, probReal_univ, one_mul] using
      hrect MeasurableSet.univ a
  have hTreal {s : Set ℝ} (hs : MeasurableSet s) : μ.real (T ⁻¹' s) = law.real s := by
    have hsum : (∑ j, q j / Q) = 1 := by rw [← Finset.sum_div, show ∑ j, q j = Q from rfl,
      div_self hQ.ne']
    simpa only [Finset.coe_univ, preimage_univ, inter_univ, hsum, mul_one] using
      hrect hs Finset.univ
  refine ⟨J, hJ, ?_, ?_, ?_, ?_, measureReal_race_slice q hq hX hlaw hind⟩
  · filter_upwards [raceWinner_spec_ae q hq hX hlaw hind] with ω hω
    change raceTime X ω = X (J ω) ω ∧ ∀ i, i ≠ J ω → raceTime X ω < X i ω
    rw [raceTime_eq_of_mem hω]
    exact ⟨rfl, hω.2⟩
  · refine ⟨hT.aemeasurable, Measure.ext fun s hs => ?_⟩
    change (μ.map T) s = law s
    rw [Measure.map_apply hT hs]
    exact (measureReal_eq_measureReal_iff (measure_ne_top μ _) (measure_ne_top law _)).mp
      (hTreal hs)
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s b hs _
    change μ (T ⁻¹' s ∩ J ⁻¹' b) = μ (T ⁻¹' s) * μ (J ⁻¹' b)
    let a : Finset (Fin (n + 1)) := Finset.univ.filter (· ∈ b)
    have ha : (↑a : Set (Fin (n + 1))) = b := by ext j; simp [a]
    have hreal := hrect hs a
    rw [← hTreal hs, ← hJreal a, ha] at hreal
    rw [← ofReal_measureReal (measure_ne_top μ (T ⁻¹' s ∩ J ⁻¹' b)), hreal,
      ENNReal.ofReal_mul measureReal_nonneg,
      ofReal_measureReal (measure_ne_top μ (T ⁻¹' s)),
      ofReal_measureReal (measure_ne_top μ (J ⁻¹' b))]
  · intro j
    simpa only [Finset.coe_singleton, Finset.sum_singleton] using hJreal {j}

end ProbabilityTheory
