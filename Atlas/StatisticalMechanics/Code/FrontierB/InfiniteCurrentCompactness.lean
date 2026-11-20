/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.FrontierB.InfiniteCurrentTopology
import Mathlib.MeasureTheory.Measure.Prokhorov

open Filter MeasureTheory Topology TopologicalSpace Set
open scoped ENNReal

namespace StatMech.FrontierB

variable {E : Type*} [Countable E]


def currentCoordinateBox (K : E → ℕ) : Set (InfiniteCurrentConfig E) :=
  Set.univ.pi (fun e => Set.Iio (K e))

omit [Countable E] in

theorem isCompact_currentCoordinateBox (K : E → ℕ) :
    IsCompact (currentCoordinateBox K) := by
  exact isCompact_univ_pi fun e => (Set.finite_Iio (K e)).isCompact

omit [Countable E] in

theorem currentCoordinateBox_compl (K : E → ℕ) :
    (currentCoordinateBox K)ᶜ = ⋃ e : E, {n | K e ≤ n e} := by
  ext n
  simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Iio, Set.mem_iUnion, Set.mem_setOf_eq, currentCoordinateBox]
  push Not
  rfl


theorem isTightMeasureSet_range_of_currentCoordinateBox
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (hbox : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : E → ℕ,
      ∀ i, ∑' e : E, (mu i : Measure _) {n : InfiniteCurrentConfig E | K e ≤ n e} ≤ ε) :
    IsTightMeasureSet (Set.range fun i => (mu i : Measure (InfiniteCurrentConfig E))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨K, hK⟩ := hbox ε hε
  refine ⟨currentCoordinateBox K, isCompact_currentCoordinateBox K, ?_⟩
  rintro m ⟨i, rfl⟩
  rw [currentCoordinateBox_compl]
  exact (measure_iUnion_le _).trans (hK i)



theorem isTightMeasureSet_range_of_coordinate_tight
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (hcoord : ∀ e : E, ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℕ, ∀ i,
      (mu i : Measure _) {n : InfiniteCurrentConfig E | K ≤ n e} ≤ ε) :
    IsTightMeasureSet (Set.range fun i =>
      (mu i : Measure (InfiniteCurrentConfig E))) := by
  apply isTightMeasureSet_range_of_currentCoordinateBox mu
  intro ε hε
  obtain ⟨δ, hδpos, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable' hε.ne' E
  choose K hK using fun e => hcoord e (δ e) (hδpos e)
  refine ⟨K, fun i => ?_⟩
  exact (ENNReal.tsum_le_tsum fun e => hK e i).trans hδsum.le



theorem isTightMeasureSet_range_of_uniform_inverse_tail
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)) (B : ℝ≥0∞)
    (hB : B ≠ ∞)
    (htail : ∀ i e (K : ℕ), 0 < K →
      (mu i : Measure _) {n : InfiniteCurrentConfig E | K ≤ n e} ≤ B / K) :
    IsTightMeasureSet (Set.range fun i =>
      (mu i : Measure (InfiniteCurrentConfig E))) := by
  apply isTightMeasureSet_range_of_coordinate_tight mu
  intro e ε hε
  obtain ⟨K, hKpos, hK⟩ := ENNReal.exists_nat_pos_mul_gt hε.ne' hB
  refine ⟨K, fun i => ?_⟩
  exact (htail i e K hKpos).trans
    (ENNReal.div_le_of_le_mul' hK.le)


theorem weakCurrent_subsequence_of_tight
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E))
    (htight : IsTightMeasureSet (Set.range fun i => (mu i : Measure (InfiniteCurrentConfig E)))) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig E)) (phi : ℕ → ℕ),
      StrictMono phi ∧ WeakCurrentConverges (mu ∘ phi) nu := by
  have hc : IsCompact (closure (Set.range mu)) := by
    apply isCompact_closure_of_isTightMeasureSet
    have heq : {m : Measure (InfiniteCurrentConfig E) |
        ∃ rho ∈ Set.range mu, (rho : Measure _) = m} =
        Set.range (fun i => (mu i : Measure (InfiniteCurrentConfig E))) := by
      ext m
      simp
    rw [heq]
    exact htight
  obtain ⟨nu, _hnu, phi, hphi, hlim⟩ :=
    hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨nu, phi, hphi, hlim⟩


theorem weakCurrent_subsequence_of_uniform_inverse_tail
    (mu : ℕ → ProbabilityMeasure (InfiniteCurrentConfig E)) (B : ℝ≥0∞)
    (hB : B ≠ ∞)
    (htail : ∀ i e (K : ℕ), 0 < K →
      (mu i : Measure _) {n : InfiniteCurrentConfig E | K ≤ n e} ≤ B / K) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig E)) (phi : ℕ → ℕ),
      StrictMono phi ∧ WeakCurrentConverges (mu ∘ phi) nu := by
  exact weakCurrent_subsequence_of_tight mu
    (isTightMeasureSet_range_of_uniform_inverse_tail mu B hB htail)

end StatMech.FrontierB
