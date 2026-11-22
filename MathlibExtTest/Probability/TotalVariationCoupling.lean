/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.TotalVariationCoupling

open MathlibExt.Probability.TotalVariationCoupling
open MathlibExt.Probability

/-- Boundary check: distance from a law to itself is `0`. -/
example {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p : PMF α) : MarkovMixing.tvDist (fun a => (p a).toReal) (fun a => (p a).toReal) = 0 := by
  simp

/-- A diagonal coupling works without any finiteness assumption. -/
example {α : Type*} (p : PMF α) : IsCoupling p p (p.map fun a => (a, a)) := by
  constructor <;> rw [PMF.map_comp] <;> exact PMF.map_id p

/-- Distinct pure laws on an infinite type use the same coupling predicate. -/
example : IsCoupling (PMF.pure (0 : ℕ)) (PMF.pure 1) (PMF.pure (0, 1)) := by
  simp [IsCoupling, PMF.pure_map]

/-- A maximal coupling exists for the pair `(p, p)`, and its
    differing probability equals the total variation. -/
example {α : Type*} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (p : PMF α) :
    ∃ r : PMF (α × α), IsCoupling p p r ∧
      (r.toMeasure {x : α × α | x.1 ≠ x.2}).toReal =
        MarkovMixing.tvDist (fun a => (p a).toReal) (fun a => (p a).toReal) :=
  exists_maximal_coupling p p

/-- Distinct pure finite laws have mismatch mass and total variation distance `1`. -/
example :
    IsCoupling (PMF.pure (0 : Fin 2)) (PMF.pure (1 : Fin 2))
        (PMF.pure ((0, 1) : Fin 2 × Fin 2)) ∧
      ((PMF.pure ((0, 1) : Fin 2 × Fin 2)).toMeasure
          {x : Fin 2 × Fin 2 | x.1 ≠ x.2}).toReal = 1 ∧
      MarkovMixing.tvDist (fun a => ((PMF.pure (0 : Fin 2)) a).toReal)
        (fun a => ((PMF.pure (1 : Fin 2)) a).toReal) = 1 := by
  refine ⟨by simp [IsCoupling, PMF.pure_map], ?_, ?_⟩
  · rw [PMF.toMeasure_pure_apply _ _ MeasurableSet.of_discrete]
    simp
  · simp [MarkovMixing.tvDist, Fin.sum_univ_two, PMF.pure_apply]
    norm_num
