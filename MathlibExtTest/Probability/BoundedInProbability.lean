/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BoundedInProbability
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace MathlibExtTest.Probability.BoundedInProbability

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- The real-valued form used by `CoxAsymptotics`: a positive radius `M` with
`P {M ≤ |X n|} ≤ ε` for every `n`. -/
example {X : ℕ → Ω → ℝ} {Z : Ω' → ℝ} (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P')
    {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ M : ℝ, 0 < M ∧ ∀ n, P {ω | M ≤ |X n ω|} ≤ ε := by
  obtain ⟨K, hK⟩ := exists_forall_measure_lt_norm_le_of_tendstoInDistribution h hε
  refine ⟨max K 0 + 1, by linarith [le_max_right K 0], fun n => le_trans ?_ (hK n)⟩
  refine measure_mono fun ω (hω : max K 0 + 1 ≤ |X n ω|) => ?_
  change K < |X n ω|
  linarith [le_max_left K 0]

/-- The vector-valued form used by `GEE.Sandwich`, in the Euclidean plane. -/
example {X : ℕ → Ω → EuclideanSpace ℝ (Fin 2)} {Z : Ω' → EuclideanSpace ℝ (Fin 2)}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P') {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : ℝ, ∀ n, P {ω | K < ‖X n ω‖} ≤ ε :=
  exists_forall_measure_lt_norm_le_of_tendstoInDistribution h hε

#print axioms exists_forall_measure_lt_norm_le_of_tendstoInDistribution

end MathlibExtTest.Probability.BoundedInProbability
