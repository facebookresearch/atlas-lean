/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.Sort.Bucket.ExpectedCost

open Set MeasureTheory ProbabilityTheory Cslib.Algorithms.Lean.TimeM Filter
open scoped BigOperators

#check @bucketSort
#check @bucketSort_empty
#check @bucketSort_perm
#check @bucketSort_sorted
#check @bucketSort_time
#check @bucketSort_time_lower
#check @bucketSort_time_le_sum_sq
#check @bucketSort_occupancy_mean
#check @bucketSort_occupancy_variance
#check @bucketSort_occupancy_secondMoment
#check @bucketSort_time_measurable
#check @bucketSort_time_integrable
#check @bucketSort_time_expected_lower
#check @bucketSort_time_expected_upper
#check @bucketSort_time_expected_zero
#check @bucketSort_time_expected_one
#check @bucketSort_time_expected_isTheta

example {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (xs : Array R) (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    5 * xs.size ≤ (bucketSort xs hx).time := bucketSort_time_lower xs hx

example {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (xs : Array R) (hx : ∀ x ∈ xs.toList, x ∈ Ico (0 : R) 1) :
    (bucketSort xs hx).time ≤ 5 * xs.size +
      ∑ i : Fin xs.size, (xs.toList.countP
        (fun x => decide (Nat.floor ((xs.size : R) * x) = i.val))) ^ 2 :=
  bucketSort_time_le_sum_sq xs hx

open Classical in
example : Asymptotics.IsTheta atTop
    (fun n : ℕ => ∫ ω : Fin n → ℝ,
      (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
        ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
      ∂Measure.pi (fun _ : Fin n => cond (volume : Measure ℝ) (Ico 0 1)))
    (fun n : ℕ => (n : ℝ)) := bucketSort_time_expected_isTheta

open Classical in
example : (∫ ω : Fin 0 → ℝ,
    (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
      ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
    ∂Measure.pi (fun _ : Fin 0 => cond (volume : Measure ℝ) (Ico 0 1))) = 0 :=
  bucketSort_time_expected_zero

open Classical in
example : (∫ ω : Fin 1 → ℝ,
    (if hx : ∀ x ∈ (Array.ofFn ω).toList, x ∈ Ico 0 1 then
      ((bucketSort (Array.ofFn ω) hx).time : ℝ) else 0)
    ∂Measure.pi (fun _ : Fin 1 => cond (volume : Measure ℝ) (Ico 0 1))) = 5 :=
  bucketSort_time_expected_one
