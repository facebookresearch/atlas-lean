/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.IdentifiableHazardContinuous

/-!
# Peterson bounds: partial identification under arbitrary dependent censoring

`PetersonIdentification` shows that, when the failure time `T` and the censoring time `C` are
independent, the law of the right-censored observation `(X, δ) = (T ∧ C, 1{T ≤ C})` identifies
the failure-time law on the at-risk set, even if the censoring law is unknown. Without
independence this fails: the joint law of `(T, C)` is an arbitrary probability measure `μ` on
`ℝ × ℝ`, and the observed-data law `P` identifies the failure-time distribution function only up
to an interval. This file proves Peterson's bounds and shows that they are sharp:

`P(X ≤ t, δ = 1) ≤ P(T ≤ t) ≤ P(X ≤ t, δ = 1) + P(X < t, δ = 0)`.

The lower bound counts observed failures by time `t`. The upper bound adds every subject censored
strictly before `t`, who could have failed between its censoring time and `t`. Ties count as
failures (`censoredObsMap`), so a subject censored at `C = t` has `T > t`. The textbook form
with `P(X ≤ t, δ = 0)` is still a valid upper bound, but it is not sharp when the censored
observations have an atom at `t`; the `X < t` form is.

## Definitions

* `jointCensoredObsLaw μ`: the observed-data law of `(T ∧ C, 1{T ≤ C})` when `(T, C) ~ μ`.
* The failure-time law, the law of `T`, is the first marginal `μ.fst` (Mathlib's
  `MeasureTheory.Measure.fst`).
* `petersonLower P t = P(X ≤ t, δ = 1)` and `petersonUpper P t = P(X ≤ t, δ = 1) + P(X < t, δ = 0)`.
* `petersonIdentifiedSet P t`: the values of `P(T ≤ t)` over all joint laws compatible with `P`.

## Main results

* `petersonLower_le_fst_Iic`, `fst_Iic_le_petersonUpper`: **Peterson's bounds**, for
  every measure `μ` on `ℝ × ℝ`.
* `petersonLower_le_censoredObsLaw`, `le_petersonUpper_censoredObsLaw`: under independent
  censoring the bounds hold for `F (Iic t)`, so they contain the point identified in
  `PetersonIdentification`.
* `jointCensoredObsLaw_lowerCoupling`, `fst_map_lowerCoupling_Iic` (and the `upperCoupling`
  versions): explicit joint laws compatible with any `P` that attain each bound.
* `petersonIdentifiedSet_eq`: **sharp partial identification**: the identified set of
  `P(T ≤ t)` is exactly the interval `[petersonLower P t, petersonUpper P t]`.
* `petersonLower_eq_petersonUpper_iff`, `fst_Iic_eq_of_jointCensoredObsLaw_eq`: the
  distribution function at `t` is point identified exactly when `P(X < t, δ = 0) = 0`.
* `exists_fst_Iic_ne_of_jointCensoredObsLaw_eq`: otherwise two joint laws with the same
  observed-data law give different values of `P(T ≤ t)`.

## Scope

Single-subject observed-data law; `μ` is any Borel measure on `ℝ × ℝ` for the bounds and any
probability measure for sharpness. Sharpness is pointwise in `t`: each value in the interval is
attained by some joint law, which may depend on `t`. The sharp identified set of the whole
failure-time law (a joint condition across all `t`) is not formalized.

## Reused API (source receipts)

* `censoredObsMap`, `measurable_censoredObsMap`, `censoredObsLaw`
  (`IdentifiableHazardContinuous.lean`); `obsTime` (`CountingProcess.lean`).
* `MeasureTheory.Measure.fst`, `Measure.fst_apply`, `Measure.fst_prod`
  (`MeasureTheory/Measure/Prod.lean`); `Measure.map_apply`, `Measure.map_map`, `Measure.map_add`,
  `Measure.map_smul` (`MeasureTheory/Measure/Map.lean`);
  `measurable_from_prod_countable_left` (`MeasureTheory/MeasurableSpace/Constructions.lean`).

## References

* A. V. Peterson, *Bounds for a joint distribution function with fixed sub-distribution functions:
  application to competing risks*, Proc. Nat. Acad. Sci. USA 73 (1976), 11–13.
* A. Tsiatis, *A nonidentifiability aspect of the problem of competing risks*, Proc. Nat. Acad.
  Sci. USA 72 (1975), 20–22.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime

open MeasureTheory Set
open scoped ENNReal

/-! ### Observed-data law under a joint law of `(T, C)` -/

/-- The **observed-data law under dependent censoring**: the pushforward of an arbitrary measure
`μ` on `ℝ × ℝ` along `censoredObsMap`. When `μ` is the joint law of `(T, C)`, it is the law of
`(T ∧ C, 1{T ≤ C})`. -/
noncomputable def jointCensoredObsLaw (μ : Measure (ℝ × ℝ)) : Measure (ℝ × Bool) :=
  μ.map censoredObsMap

/-- Independent censoring is the special case `μ = F ⊗ G`. -/
theorem censoredObsLaw_eq_jointCensoredObsLaw (F G : Measure ℝ) :
    censoredObsLaw F G = jointCensoredObsLaw (F.prod G) := rfl

/-! ### Peterson's bounds -/

/-- **Peterson lower bound** `P((-∞, t] × {true})` of a measure `P` on `ℝ × Bool`: the observed
failures by time `t`, `P(X ≤ t, δ = 1)` for an observed-data law. -/
noncomputable def petersonLower (P : Measure (ℝ × Bool)) (t : ℝ) : ℝ≥0∞ :=
  P (Iic t ×ˢ {true})

/-- **Peterson upper bound** `P((-∞, t] × {true}) + P((-∞, t) × {false})` of a measure `P` on
`ℝ × Bool`: the observed failures by time `t` plus the subjects censored strictly before `t`,
`P(X ≤ t, δ = 1) + P(X < t, δ = 0)` for an observed-data law. -/
noncomputable def petersonUpper (P : Measure (ℝ × Bool)) (t : ℝ) : ℝ≥0∞ :=
  P (Iic t ×ˢ {true}) + P (Iio t ×ˢ {false})

/-- The **identified set** of `P(T ≤ t)`: its values over all joint laws of `(T, C)` that
produce the observed-data law `P`. -/
def petersonIdentifiedSet (P : Measure (ℝ × Bool)) (t : ℝ) : Set ℝ≥0∞ :=
  {v | ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧ jointCensoredObsLaw μ = P ∧
    μ.fst (Iic t) = v}

private lemma measurableSet_Iic_prod (t : ℝ) (b : Bool) :
    MeasurableSet (Iic t ×ˢ ({b} : Set Bool)) :=
  measurableSet_Iic.prod (measurableSet_singleton b)

private lemma measurableSet_Iio_prod (t : ℝ) (b : Bool) :
    MeasurableSet (Iio t ×ˢ ({b} : Set Bool)) :=
  measurableSet_Iio.prod (measurableSet_singleton b)

/-- `P(X ≤ t, δ = 1) = μ(T ≤ t, T ≤ C)`. -/
theorem jointCensoredObsLaw_Iic_true (μ : Measure (ℝ × ℝ)) (t : ℝ) :
    jointCensoredObsLaw μ (Iic t ×ˢ {true}) = μ {ω | ω.1 ≤ t ∧ ω.1 ≤ ω.2} := by
  rw [jointCensoredObsLaw, Measure.map_apply measurable_censoredObsMap (measurableSet_Iic_prod _ _)]
  congr 1
  ext ⟨x, c⟩
  simp only [censoredObsMap, obsTime, mem_preimage, mem_prod, mem_Iic, mem_singleton_iff,
    decide_eq_true_eq, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [min_eq_left h2] at h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(min_le_left _ _).trans h1, h2⟩

/-- `P(X < t, δ = 0) = μ(C < t, C < T)`. -/
theorem jointCensoredObsLaw_Iio_false (μ : Measure (ℝ × ℝ)) (t : ℝ) :
    jointCensoredObsLaw μ (Iio t ×ˢ {false}) = μ {ω | ω.2 < t ∧ ω.2 < ω.1} := by
  rw [jointCensoredObsLaw, Measure.map_apply measurable_censoredObsMap (measurableSet_Iio_prod _ _)]
  congr 1
  ext ⟨x, c⟩
  simp only [censoredObsMap, obsTime, mem_preimage, mem_prod, mem_Iio, mem_singleton_iff,
    decide_eq_false_iff_not, not_le, mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rwa [min_eq_right h2.le] at h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(min_le_right _ _).trans_lt h1, h2⟩

/-- **Peterson lower bound**: for every measure `μ` on `ℝ × ℝ` with observed-data measure `P`,
`P((-∞, t] × {true}) ≤ μ((-∞, t] × univ)`; for a joint law of `(T, C)` this is
`P(X ≤ t, δ = 1) ≤ P(T ≤ t)`. -/
theorem petersonLower_le_fst_Iic (μ : Measure (ℝ × ℝ)) (t : ℝ) :
    petersonLower (jointCensoredObsLaw μ) t ≤ μ.fst (Iic t) := by
  rw [petersonLower, jointCensoredObsLaw_Iic_true, Measure.fst_apply measurableSet_Iic]
  exact measure_mono fun ω hω => hω.1

/-- **Peterson upper bound**: for every measure `μ` on `ℝ × ℝ` with observed-data measure `P`,
`μ((-∞, t] × univ) ≤ P((-∞, t] × {true}) + P((-∞, t) × {false})`; for a joint law of `(T, C)`
this is `P(T ≤ t) ≤ P(X ≤ t, δ = 1) + P(X < t, δ = 0)`. -/
theorem fst_Iic_le_petersonUpper (μ : Measure (ℝ × ℝ)) (t : ℝ) :
    μ.fst (Iic t) ≤ petersonUpper (jointCensoredObsLaw μ) t := by
  rw [petersonUpper, jointCensoredObsLaw_Iic_true, jointCensoredObsLaw_Iio_false,
    Measure.fst_apply measurableSet_Iic]
  have hsub : Prod.fst ⁻¹' Iic t ⊆
      {ω : ℝ × ℝ | ω.1 ≤ t ∧ ω.1 ≤ ω.2} ∪ {ω : ℝ × ℝ | ω.2 < t ∧ ω.2 < ω.1} := by
    intro ω hω
    have hω' : ω.1 ≤ t := hω
    by_cases h : ω.1 ≤ ω.2
    · exact Or.inl ⟨hω', h⟩
    · have h' : ω.2 < ω.1 := not_le.1 h
      exact Or.inr ⟨h'.trans_le hω', h'⟩
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- The Peterson bounds are ordered. -/
theorem petersonLower_le_petersonUpper (P : Measure (ℝ × Bool)) (t : ℝ) :
    petersonLower P t ≤ petersonUpper P t :=
  le_self_add

/-- **Under independent censoring the Peterson bounds contain the identified value**: for an
s-finite `F` and a probability measure `G`, the observed-data measure `P` of `(F, G)` satisfies
`P((-∞, t] × {true}) ≤ F(-∞, t]`. -/
theorem petersonLower_le_censoredObsLaw (F G : Measure ℝ) [SFinite F] [IsProbabilityMeasure G]
    (t : ℝ) : petersonLower (censoredObsLaw F G) t ≤ F (Iic t) := by
  have h := petersonLower_le_fst_Iic (F.prod G) t
  rwa [Measure.fst_prod] at h

/-- **Under independent censoring the Peterson bounds contain the identified value**: for an
s-finite `F` and a probability measure `G`, the observed-data measure `P` of `(F, G)` satisfies
`F(-∞, t] ≤ P((-∞, t] × {true}) + P((-∞, t) × {false})`. -/
theorem le_petersonUpper_censoredObsLaw (F G : Measure ℝ) [SFinite F] [IsProbabilityMeasure G]
    (t : ℝ) : F (Iic t) ≤ petersonUpper (censoredObsLaw F G) t := by
  have h := fst_Iic_le_petersonUpper (F.prod G) t
  rwa [Measure.fst_prod] at h

/-! ### Sharpness: joint laws attaining the bounds -/

/-- `censoredObsMap (x, x) = (x, failure)`. -/
private lemma censoredObsMap_diag (x : ℝ) : censoredObsMap (x, x) = (x, true) := by
  simp [censoredObsMap, obsTime]

/-- `censoredObsMap (s, x) = (x, censored)` when `x < s`. -/
private lemma censoredObsMap_of_lt {s x : ℝ} (h : x < s) : censoredObsMap (s, x) = (x, false) := by
  simp [censoredObsMap, obsTime, min_eq_right h.le, not_le.2 h]

/-- The coupling attaining the **lower** bound at `t`: an observed failure at `x` is `T = C = x`;
an observation censored at `x` is `C = x` with `T = max x t + 1 > t`, so it never fails by `t`. -/
noncomputable def lowerCoupling (t : ℝ) (p : ℝ × Bool) : ℝ × ℝ :=
  (cond p.2 p.1 (max p.1 t + 1), p.1)

/-- The coupling attaining the **upper** bound at `t`: an observed failure at `x` is `T = C = x`;
an observation censored at `x < t` is `C = x` with `T = t`, so it fails by `t`, and one censored
at `x ≥ t` has `T = x + 1`. -/
noncomputable def upperCoupling (t : ℝ) (p : ℝ × Bool) : ℝ × ℝ :=
  (cond p.2 p.1 (if p.1 < t then t else p.1 + 1), p.1)

theorem measurable_lowerCoupling (t : ℝ) : Measurable (lowerCoupling t) := by
  refine measurable_from_prod_countable_left fun b => ?_
  cases b
  · exact (((measurable_id.max measurable_const).add_const 1).prodMk measurable_id :
      Measurable fun x : ℝ => (max x t + 1, x))
  · exact (measurable_id.prodMk measurable_id : Measurable fun x : ℝ => (x, x))

theorem measurable_upperCoupling (t : ℝ) : Measurable (upperCoupling t) := by
  refine measurable_from_prod_countable_left fun b => ?_
  cases b
  · exact ((Measurable.ite (p := fun x : ℝ => x < t) measurableSet_Iio measurable_const
      (measurable_id.add_const 1)).prodMk measurable_id :
        Measurable fun x : ℝ => (if x < t then t else x + 1, x))
  · exact (measurable_id.prodMk measurable_id : Measurable fun x : ℝ => (x, x))

theorem censoredObsMap_comp_lowerCoupling (t : ℝ) : censoredObsMap ∘ lowerCoupling t = id := by
  funext ⟨x, b⟩
  cases b
  · change censoredObsMap (max x t + 1, x) = (x, false)
    exact censoredObsMap_of_lt ((le_max_left x t).trans_lt (lt_add_one _))
  · exact censoredObsMap_diag x

theorem censoredObsMap_comp_upperCoupling (t : ℝ) : censoredObsMap ∘ upperCoupling t = id := by
  funext ⟨x, b⟩
  cases b
  · change censoredObsMap (if x < t then t else x + 1, x) = (x, false)
    refine censoredObsMap_of_lt ?_
    split_ifs with h
    · exact h
    · linarith [not_lt.1 h]
  · exact censoredObsMap_diag x

theorem lowerCoupling_preimage_fst_Iic (t : ℝ) :
    lowerCoupling t ⁻¹' (Prod.fst ⁻¹' Iic t) = Iic t ×ˢ {true} := by
  ext ⟨x, b⟩
  cases b
  · have : ¬ max x t + 1 ≤ t := not_le.2 ((le_max_right x t).trans_lt (lt_add_one _))
    simp [lowerCoupling, this]
  · simp [lowerCoupling]

theorem upperCoupling_preimage_fst_Iic (t : ℝ) :
    upperCoupling t ⁻¹' (Prod.fst ⁻¹' Iic t) = Iic t ×ˢ {true} ∪ Iio t ×ˢ {false} := by
  ext ⟨x, b⟩
  cases b
  · by_cases h : x < t
    · simp [upperCoupling, h]
    · have : ¬ x + 1 ≤ t := fun h' => h (by linarith)
      simp [upperCoupling, h, this]
  · simp [upperCoupling]

/-- The lower coupling reproduces the observed-data law. -/
theorem jointCensoredObsLaw_lowerCoupling (P : Measure (ℝ × Bool)) (t : ℝ) :
    jointCensoredObsLaw (P.map (lowerCoupling t)) = P := by
  rw [jointCensoredObsLaw, Measure.map_map measurable_censoredObsMap (measurable_lowerCoupling t),
    censoredObsMap_comp_lowerCoupling, Measure.map_id]

/-- The upper coupling reproduces the observed-data law. -/
theorem jointCensoredObsLaw_upperCoupling (P : Measure (ℝ × Bool)) (t : ℝ) :
    jointCensoredObsLaw (P.map (upperCoupling t)) = P := by
  rw [jointCensoredObsLaw, Measure.map_map measurable_censoredObsMap (measurable_upperCoupling t),
    censoredObsMap_comp_upperCoupling, Measure.map_id]

/-- The lower coupling attains the lower bound. -/
theorem fst_map_lowerCoupling_Iic (P : Measure (ℝ × Bool)) (t : ℝ) :
    (P.map (lowerCoupling t)).fst (Iic t) = petersonLower P t := by
  rw [Measure.fst_apply measurableSet_Iic,
    Measure.map_apply (measurable_lowerCoupling t) (measurable_fst measurableSet_Iic),
    lowerCoupling_preimage_fst_Iic, petersonLower]

/-- The upper coupling attains the upper bound. -/
theorem fst_map_upperCoupling_Iic (P : Measure (ℝ × Bool)) (t : ℝ) :
    (P.map (upperCoupling t)).fst (Iic t) = petersonUpper P t := by
  rw [Measure.fst_apply measurableSet_Iic,
    Measure.map_apply (measurable_upperCoupling t) (measurable_fst measurableSet_Iic),
    upperCoupling_preimage_fst_Iic, petersonUpper,
    measure_union (disjoint_prod.2 (Or.inr (disjoint_singleton.2 (by decide))))
      (measurableSet_Iio_prod _ _)]

/-! ### The sharp identified set -/

/-- A probability mixture `a μ₀ + (1 - a) μ₁` of probability measures, with `0 ≤ a ≤ 1` real. -/
private lemma isProbabilityMeasure_mix {α : Type*} [MeasurableSpace α] (μ₀ μ₁ : Measure α)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁] {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    IsProbabilityMeasure (ENNReal.ofReal a • μ₀ + ENNReal.ofReal (1 - a) • μ₁) := by
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ, measure_univ,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, ← ENNReal.ofReal_add ha0 (sub_nonneg.2 ha1),
    (by ring : a + (1 - a) = 1), ENNReal.ofReal_one]

/-- **Sharp partial identification (Peterson).** For any observed-data probability law `P`, the
values of `P(T ≤ t)` over all joint laws of `(T, C)` producing `P` form exactly the interval
`[P(X ≤ t, δ = 1), P(X ≤ t, δ = 1) + P(X < t, δ = 0)]`. -/
theorem petersonIdentifiedSet_eq (P : Measure (ℝ × Bool)) [IsProbabilityMeasure P] (t : ℝ) :
    petersonIdentifiedSet P t = Icc (petersonLower P t) (petersonUpper P t) := by
  ext v
  constructor
  · rintro ⟨μ, -, hμ, rfl⟩
    rw [← hμ]
    exact ⟨petersonLower_le_fst_Iic μ t, fst_Iic_le_petersonUpper μ t⟩
  rintro ⟨hlo, hhi⟩
  rcases eq_or_lt_of_le (hlo.trans hhi) with heq | hlt
  · exact ⟨P.map (lowerCoupling t), inferInstance, jointCensoredObsLaw_lowerCoupling P t,
      (fst_map_lowerCoupling_Iic P t).trans (le_antisymm hlo (hhi.trans heq.ge))⟩
  have hhi_top : petersonUpper P t ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩
  have hv_top : v ≠ ∞ := ne_top_of_le_ne_top hhi_top hhi
  have hlo_top : petersonLower P t ≠ ∞ := ne_top_of_le_ne_top hv_top hlo
  have hlt' : (petersonLower P t).toReal < (petersonUpper P t).toReal :=
    ENNReal.toReal_strict_mono hhi_top hlt
  have hlo' : (petersonLower P t).toReal ≤ v.toReal := ENNReal.toReal_mono hv_top hlo
  have hhi' : v.toReal ≤ (petersonUpper P t).toReal := ENNReal.toReal_mono hhi_top hhi
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ((petersonUpper P t).toReal - v.toReal) /
      ((petersonUpper P t).toReal - (petersonLower P t).toReal) := ⟨_, rfl⟩
  have hd : (petersonUpper P t).toReal - (petersonLower P t).toReal ≠ 0 :=
    (sub_pos.2 hlt').ne'
  have ha0 : 0 ≤ a := ha ▸ div_nonneg (sub_nonneg.2 hhi') (sub_nonneg.2 hlt'.le)
  have ha1 : a ≤ 1 := ha ▸ (div_le_one (sub_pos.2 hlt')).2 (by linarith)
  have hmul : a * ((petersonUpper P t).toReal - (petersonLower P t).toReal) =
      (petersonUpper P t).toReal - v.toReal := by
    rw [ha]
    exact div_mul_cancel₀ _ hd
  have hsum : ENNReal.ofReal a + ENNReal.ofReal (1 - a) = 1 := by
    rw [← ENNReal.ofReal_add ha0 (sub_nonneg.2 ha1), (by ring : a + (1 - a) = 1),
      ENNReal.ofReal_one]
  refine ⟨ENNReal.ofReal a • P.map (lowerCoupling t) +
    ENNReal.ofReal (1 - a) • P.map (upperCoupling t), isProbabilityMeasure_mix _ _ ha0 ha1, ?_, ?_⟩
  · rw [jointCensoredObsLaw, Measure.map_add _ _ measurable_censoredObsMap,
      Measure.map_smul _ measurable_censoredObsMap.aemeasurable,
      Measure.map_smul _ measurable_censoredObsMap.aemeasurable, ← jointCensoredObsLaw,
      ← jointCensoredObsLaw,
      jointCensoredObsLaw_lowerCoupling, jointCensoredObsLaw_upperCoupling, ← add_smul, hsum,
      one_smul]
  · rw [Measure.fst_apply measurableSet_Iic, Measure.add_apply, Measure.smul_apply,
      Measure.smul_apply, ← Measure.fst_apply measurableSet_Iic,
      ← Measure.fst_apply measurableSet_Iic,
      fst_map_lowerCoupling_Iic, fst_map_upperCoupling_Iic, smul_eq_mul, smul_eq_mul,
      ← ENNReal.ofReal_toReal hlo_top, ← ENNReal.ofReal_toReal hhi_top,
      ← ENNReal.ofReal_toReal hv_top, ← ENNReal.ofReal_mul ha0,
      ← ENNReal.ofReal_mul (sub_nonneg.2 ha1),
      ← ENNReal.ofReal_add (mul_nonneg ha0 ENNReal.toReal_nonneg)
        (mul_nonneg (sub_nonneg.2 ha1) ENNReal.toReal_nonneg)]
    congr 1
    linarith

/-- Every value in the Peterson interval is attained by a joint law compatible with `P`. -/
theorem exists_jointCensoredObsLaw_eq_fst_Iic_eq (P : Measure (ℝ × Bool))
    [IsProbabilityMeasure P] {t : ℝ} {v : ℝ≥0∞} (hlo : petersonLower P t ≤ v)
    (hhi : v ≤ petersonUpper P t) :
    ∃ μ : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧ jointCensoredObsLaw μ = P ∧
      μ.fst (Iic t) = v := by
  have hv : v ∈ petersonIdentifiedSet P t := by
    rw [petersonIdentifiedSet_eq]
    exact ⟨hlo, hhi⟩
  exact hv

/-! ### When is `P(T ≤ t)` point identified? -/

/-- The Peterson interval collapses to a point exactly when no subject is censored strictly
before `t`. -/
theorem petersonLower_eq_petersonUpper_iff (P : Measure (ℝ × Bool)) [IsFiniteMeasure P] (t : ℝ) :
    petersonLower P t = petersonUpper P t ↔ P (Iio t ×ˢ {false}) = 0 := by
  have h := ENNReal.add_right_inj (a := P (Iic t ×ˢ {true})) (b := P (Iio t ×ˢ {false}))
    (c := 0) (measure_ne_top _ _)
  rw [add_zero] at h
  rw [petersonLower, petersonUpper, eq_comm]
  exact h

/-- **Point identification without early censoring.** If two measures `μ`, `μ'` on `ℝ × ℝ` have
the same observed-data measure `P` and `P((-∞, t) × {false}) = 0` (no subject is censored strictly
before `t`), then `μ((-∞, t] × univ) = μ'((-∞, t] × univ)`: for joint laws, the same `P(T ≤ t)`.
-/
theorem fst_Iic_eq_of_jointCensoredObsLaw_eq {μ μ' : Measure (ℝ × ℝ)}
    (heq : jointCensoredObsLaw μ = jointCensoredObsLaw μ') {t : ℝ}
    (h0 : jointCensoredObsLaw μ (Iio t ×ˢ {false}) = 0) :
    μ.fst (Iic t) = μ'.fst (Iic t) := by
  have hub : ∀ ν : Measure (ℝ × ℝ), jointCensoredObsLaw ν (Iio t ×ˢ {false}) = 0 →
      ν.fst (Iic t) = petersonLower (jointCensoredObsLaw ν) t := fun ν hν =>
    le_antisymm ((fst_Iic_le_petersonUpper ν t).trans_eq (by rw [petersonUpper, hν,
      add_zero, petersonLower])) (petersonLower_le_fst_Iic ν t)
  rw [hub μ h0, hub μ' (heq ▸ h0), heq]

/-- **Non-identification under dependent censoring.** If some subjects are censored strictly
before `t`, there are two joint laws of `(T, C)` with the same observed-data law `P` and different
values of `P(T ≤ t)`. -/
theorem exists_fst_Iic_ne_of_jointCensoredObsLaw_eq (P : Measure (ℝ × Bool))
    [IsProbabilityMeasure P] {t : ℝ} (h0 : P (Iio t ×ˢ {false}) ≠ 0) :
    ∃ μ μ' : Measure (ℝ × ℝ), IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      jointCensoredObsLaw μ = P ∧ jointCensoredObsLaw μ' = P ∧
      μ.fst (Iic t) ≠ μ'.fst (Iic t) := by
  refine ⟨P.map (lowerCoupling t), P.map (upperCoupling t), inferInstance, inferInstance,
    jointCensoredObsLaw_lowerCoupling P t, jointCensoredObsLaw_upperCoupling P t, ?_⟩
  rw [fst_map_lowerCoupling_Iic, fst_map_upperCoupling_Iic]
  exact fun h => h0 ((petersonLower_eq_petersonUpper_iff P t).1 h)

end MathlibExt.Probability.Statistics.CountingProcess.ContinuousTime
