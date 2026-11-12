/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TotalVariationCoupling

open MathlibExt.Probability.TotalVariationCoupling

/-- Boundary check: distance from a law to itself is `0`. -/
example {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p : PMF α) : tvDist p p = 0 := by
  simp [tvDist]

/-- A maximal coupling exists for the pair `(p, p)`, and its
differing probability equals the (zero) total variation, as a
statement instance. -/
example {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p : PMF α) :
    ∃ r : PMF (α × α), IsCoupling p p r ∧
      (r.toMeasure {x : α × α | x.1 ≠ x.2}).toReal = tvDist p p :=
  exists_maximal_coupling p p

/-- Nontrivial coupling: the distinct pure PMFs on `Fin 2` are coupled by
the pure joint law on `(0, 1)`. The coupling has mismatch mass `1` and
total variation distance `1`, so the coupling inequality is sharp here. -/
example :
    IsCoupling (PMF.pure (0 : Fin 2)) (PMF.pure (1 : Fin 2))
        (PMF.pure ((0, 1) : Fin 2 × Fin 2)) ∧
      ((PMF.pure ((0, 1) : Fin 2 × Fin 2)).toMeasure
          {x : Fin 2 × Fin 2 | x.1 ≠ x.2}).toReal = 1 ∧
      tvDist (PMF.pure (0 : Fin 2)) (PMF.pure (1 : Fin 2)) = 1 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro a
    fin_cases a <;> simp [PMF.pure_apply]
  · intro b
    fin_cases b <;> simp [PMF.pure_apply]
  · rw [PMF.toMeasure_pure_apply _ _ MeasurableSet.of_discrete]
    simp
  · simp [tvDist, Fin.sum_univ_two, PMF.pure_apply]
    norm_num
