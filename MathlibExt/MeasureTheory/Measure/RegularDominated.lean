/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Regularity inherited from finite measure domination

On an R₁ Borel space, a measure dominated by a finite regular measure is regular. The sum of two
finite regular measures is regular, and domination by a finite nonnegative scalar multiple also
gives regularity.

No compactness, metrizability or countability hypothesis is needed.
-/

@[expose] public section

open Set
open scoped ENNReal NNReal

namespace MeasureTheory.Measure.Regular

universe u

variable {X : Type u} [TopologicalSpace X] [R1Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Regular measure under domination by a finite regular measure.** Let `X` be an R₁
topological space with its Borel measurable structure. if `μ` is finite and regular and
`ν≤μ`, then `ν` is regular. -/
theorem of_le {nu mu : Measure X} [mu.Regular] [IsFiniteMeasure mu]
    (h : nu ≤ mu) : nu.Regular := by
  let : IsFiniteMeasure nu := isFiniteMeasure_of_le mu h
  let : InnerRegularCompactLTTop nu := by
    refine ⟨?_⟩
    intro A hA r hr
    have heps : nu A - r ≠ 0 := (tsub_pos_of_lt hr).ne'
    obtain ⟨K, hKA, hKcompact, _hKclosed, hmuK⟩ :=
      hA.1.exists_isCompact_isClosed_sdiff_lt (measure_ne_top mu A) heps
    refine ⟨K, hKA, hKcompact, ?_⟩
    have hnuK : nu (A \ K) < nu A - r :=
      (h (A \ K)).trans_lt hmuK
    have hdiff : nu A - nu K < nu A - r :=
      le_measure_sdiff.trans_lt hnuK
    exact lt_of_tsub_lt_tsub_left hdiff
  infer_instance

/-- **Regularity of the sum of finite regular measures.** Let `X` be an R₁ topological space
with its Borel measurable structure. if `μ,ν` are finite regular measures, then `μ+ν` is
regular. -/
theorem add_of_finite (mu nu : Measure X) [mu.Regular] [nu.Regular]
    [IsFiniteMeasure mu] [IsFiniteMeasure nu] : (mu + nu).Regular := by
  infer_instance

/-- **Regularity under finite nonnegative scalar domination.** Let `X` be an R₁ topological
space with its Borel measurable structure. if `μ` is finite regular, `c∈ℝ≥0` and `ν≤c •
μ`, then `ν` is regular, including `c=0`. -/
theorem of_le_nnreal_smul {nu mu : Measure X} [mu.Regular] [IsFiniteMeasure mu]
    (c : ℝ≥0) (h : nu ≤ c • mu) : nu.Regular := by
  let : (c • mu).Regular := by infer_instance
  let : IsFiniteMeasure (c • mu) := by infer_instance
  exact of_le h

end MeasureTheory.Measure.Regular
