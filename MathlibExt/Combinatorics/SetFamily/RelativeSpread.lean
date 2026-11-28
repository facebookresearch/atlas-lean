/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Spread families and spread measures

For a finite ground type `α`, its subsets are represented by `Finset α`. The upper event
of `S` consists of the sets containing `S`. A multiset family is `κ`-spread if the number
of occurrences in each upper event is at most `κ⁻¹ ^ S.card` times the total number of
occurrences. For a probability measure the corresponding bound is on the mass of the event.
We take real `κ > 1`; the parameter called `q` for measures in the source is `κ⁻¹`.

Sampling an occurrence of a nonempty multiset uniformly gives precisely the relative
frequencies of upper events, even when several occurrences give the same set. Nothing
requires enumerating the ground type: on an infinite type the same definitions test all
finite `S` against a law on finite sets.

## Reference

K. Frankston, J. Kahn, B. Narayanan and J. Park, *Thresholds versus fractional
expectation-thresholds*, arXiv:1910.13433v2, p. 3, display (4) and the paragraph following it.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace SetFamily

variable {α : Type*}

open scoped Classical in
/-- A multiset family is relatively `κ`-spread, for a real `κ > 1`, if for every finite
`S` the number of occurrences containing `S` is at most `(1/κ)^|S|` times the total
number of occurrences. The zero family satisfies this unnormalised bound. -/
def IsRelSpread (F : Multiset (Finset α)) (κ : Set.Ioi (1 : ℝ)) : Prop :=
  ∀ S : Finset α, (F.countP (S ⊆ ·) : ℝ) ≤ (κ.val⁻¹) ^ S.card * F.card

/-- A probability measure on finite sets is relatively `κ`-spread, for a real `κ > 1`,
if the mass of the sets containing each finite `S` is at most `(1/κ)^|S|`. In particular,
the test at the empty set compares the full probability mass with one. -/
def IsRelSpreadMeasure (μ : ProbabilityMeasure (Finset α)) (κ : Set.Ioi (1 : ℝ)) : Prop :=
  ∀ S : Finset α, (μ {T | S ⊆ T} : ℝ) ≤ (κ.val⁻¹) ^ S.card

end SetFamily

open scoped Classical in
/-- For the occurrence measure of a multiset `F`, the mass of a measurable event `A` is
its number of matching occurrences divided by `F.card`. For `F = 0` the measure is zero,
and the right side is zero by the extended nonnegative reals' division convention. -/
theorem MeasureTheory.Measure.ofMultiset_apply_event {β : Type*} [MeasurableSpace β]
    (F : Multiset β) {A : Set β} (hA : MeasurableSet A) :
    Measure.ofMultiset F A = (F.countP (· ∈ A) : ℝ≥0∞) / F.card := by
  classical
  have count_sum := Multiset.sum_count_eq_card (s := F.toFinset) (m := F.filter (· ∈ A))
    (fun a ha => Multiset.mem_toFinset.mpr (Multiset.mem_filter.mp ha).1)
  rw [Measure.ofMultiset, FunLike.coe_sum, Finset.sum_apply,
    Multiset.countP_eq_card_filter, ← count_sum, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ A <;> simp [Measure.dirac_apply' _ hA, ha, div_eq_mul_inv]

namespace SetFamily

variable {α : Type*}

/-- The law of a uniformly sampled occurrence in a nonempty multiset `F` of finite sets.
Its underlying measure is `Measure.ofMultiset F`: a set occurring `k` times receives
`k / F.card` of the mass. An empty multiset admits no such draw. -/
noncomputable def uniformOccurrenceMeasure (F : Multiset (Finset α)) (hF : F ≠ 0) :
    ProbabilityMeasure (Finset α) := by
  refine ⟨Measure.ofMultiset F, ⟨?_⟩⟩
  rw [Measure.ofMultiset_apply_event F MeasurableSet.univ]
  have hc : F.card ≠ 0 := fun h => hF (Multiset.card_eq_zero.mp h)
  simpa [Multiset.countP_eq_card_filter] using
    ENNReal.div_self (by exact_mod_cast hc : (F.card : ℝ≥0∞) ≠ 0) (ENNReal.natCast_ne_top _)

open scoped Classical in
/-- Under uniform occurrence sampling from a nonempty `F`, the probability of containing
`S` is the number of occurrences containing `S` divided by the total number of occurrences. -/
theorem uniformOccurrenceMeasure_superset (F : Multiset (Finset α)) (hF : F ≠ 0) (S : Finset α) :
    (uniformOccurrenceMeasure F hF {T | S ⊆ T} : ℝ) = (F.countP (S ⊆ ·) : ℝ) / F.card := by
  have hm : MeasurableSet {T : Finset α | S ⊆ T} := by
    have he : {T : Finset α | S ⊆ T} = ⋂ a ∈ S, {T : Finset α | a ∈ T} := by
      ext T
      simp [Finset.subset_iff]
    rw [he]
    exact S.measurableSet_biInter (fun a _ => measurableSet_mem_finset a)
  change (Measure.ofMultiset F {T | S ⊆ T}).toReal = _
  rw [Measure.ofMultiset_apply_event F hm, ENNReal.toReal_div]
  simp

/-- For a nonempty multiset `F` of finite sets and real `κ > 1`, the relative counting
condition for `κ`-spreadness holds if and only if the law uniform on occurrences of `F`
satisfies the upper-event probability bounds with parameter `q = 1/κ`. -/
theorem isRelSpread_iff_uniformOccurrenceMeasure (F : Multiset (Finset α)) (hF : F ≠ 0)
    (κ : Set.Ioi (1 : ℝ)) :
    IsRelSpread F κ ↔ IsRelSpreadMeasure (uniformOccurrenceMeasure F hF) κ := by
  have hpos : (0 : ℝ) < F.card := by exact_mod_cast Multiset.card_pos.mpr hF
  unfold IsRelSpread IsRelSpreadMeasure
  exact forall_congr' fun S => by rw [uniformOccurrenceMeasure_superset, div_le_iff₀ hpos]

end SetFamily
