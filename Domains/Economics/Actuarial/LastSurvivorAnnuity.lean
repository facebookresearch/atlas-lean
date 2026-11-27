/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Economics.Finance.DatedCashFlow
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real

/-!
# Last-survivor annuity values

An instalment pays its benefit if the lifetime is strictly greater than its payment time.
Taking the expected present value of these payments gives a finite sum weighted by survival
probabilities. For two lives on the same probability space, the last-survivor annuity uses the
maximum lifetime and the joint-life annuity the minimum. Inclusion–exclusion at each time gives
`lifeAnnuityValue_max`; the two lifetimes need not be independent.

## Reference

Tom Struppeck, *Life Contingencies Study Note for CAS Exam S*, revised September 19, 2015,
pp. 11–12 (joint lives): the two single-life unit payments together pay one unit if either life
survives and an additional unit if both survive. Here the same identity is weighted by
deterministic benefits and discount factors over any finite payment schedule.
-/

@[expose] public section

namespace Actuarial

open MeasureTheory MathlibExt.Economics.Finance
open scoped NNReal

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
variable (s : Finset ℕ) (date : ℕ → ℝ≥0) (benefit discount : ℕ → ℝ)

/-- Expected present value of payments contingent on survival. The indices `k ∈ s` label
instalments; `date k` is the actual time, which need not be an integer. A death at `date k`
earns no payment at that time. The expectation is for a measurable lifetime under a probability
measure, as in `lifeAnnuityValue_eq_sum`. -/
noncomputable def lifeAnnuityValue (T : Ω → ℝ≥0) : ℝ :=
  ∫ ω, presentValue discount s (fun k ↦ {a | date k < T a}.indicator (fun _ ↦ benefit k) ω) ∂P

variable [IsProbabilityMeasure P]

/-- The expected present value is the sum of the discounted benefits times the probabilities
of the actual survival events. Arbitrary real benefits and discount factors are allowed. -/
theorem lifeAnnuityValue_eq_sum {T : Ω → ℝ≥0} (hT : Measurable T) :
    lifeAnnuityValue P s date benefit discount T =
      ∑ k ∈ s, discount k * (P.real {ω | date k < T ω} * benefit k) := by
  have hm (k : ℕ) : MeasurableSet {ω | date k < T ω} := hT measurableSet_Ioi
  unfold lifeAnnuityValue presentValue
  rw [integral_finsetSum s fun k _ ↦ ((integrable_const (benefit k)).indicator (hm k)).const_mul _]
  exact Finset.sum_congr rfl fun k _ ↦ by
    rw [integral_const_mul, integral_indicator_const _ (hm k), smul_eq_mul]

/-- Last-survivor inclusion–exclusion: the value payable while either life survives equals
the sum of the two single-life values minus the value payable while both survive. The joint-life
term uses the actual minimum lifetime, not a product of marginal survival probabilities. -/
theorem lifeAnnuityValue_max {X Y : Ω → ℝ≥0} (hX : Measurable X) (hY : Measurable Y) :
    lifeAnnuityValue P s date benefit discount (fun ω ↦ max (X ω) (Y ω)) =
      lifeAnnuityValue P s date benefit discount X + lifeAnnuityValue P s date benefit discount Y -
        lifeAnnuityValue P s date benefit discount (fun ω ↦ min (X ω) (Y ω)) := by
  have perDate (t : ℝ≥0) : P.real {ω | t < max (X ω) (Y ω)} =
      P.real {ω | t < X ω} + P.real {ω | t < Y ω} - P.real {ω | t < min (X ω) (Y ω)} := by
    have either : {ω | t < max (X ω) (Y ω)} = {ω | t < X ω} ∪ {ω | t < Y ω} :=
      Set.ext fun _ ↦ lt_max_iff
    have both : {ω | t < min (X ω) (Y ω)} = {ω | t < X ω} ∩ {ω | t < Y ω} :=
      Set.ext fun _ ↦ lt_min_iff
    rw [either, both]
    exact eq_sub_of_add_eq (measureReal_union_add_inter (hY measurableSet_Ioi))
  rw [lifeAnnuityValue_eq_sum _ _ _ _ _ (hX.max hY), lifeAnnuityValue_eq_sum _ _ _ _ _ hX,
    lifeAnnuityValue_eq_sum _ _ _ _ _ hY, lifeAnnuityValue_eq_sum _ _ _ _ _ (hX.min hY),
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [perDate, sub_mul, add_mul, mul_sub, mul_add]

end Actuarial
