/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.LocalCurrentTail
import Code.FrontierB.InfiniteCurrentFiniteMarginals

open Filter MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Sharpness Lattice



theorem freeBoxCurrentMeasure_edge_inverse_tail_le
    (d n : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : Sym2 (Site d)) (K : ℕ) (hK : 0 < K) :
    (freeBoxCurrentMeasure d n beta hbeta :
      Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤
      ENNReal.ofReal (Real.exp beta) / K := by
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d n)
  · obtain ⟨f, rfl⟩ := he
    rw [freeBoxCurrentMeasure_edge_tail]
    calc
      (sourcelessCurrentMeasure (StatMech.FK.boxGraph d n) beta
          (fun _ => 1) hbeta (fun _ => by positivity) :
          Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m f} ≤
          ENNReal.ofReal (Real.exp (beta * (fun _ => (1 : ℝ)) f.1) / K) :=
        sourcelessCurrentMeasure_edge_inverse_tail_le
          (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta
          (fun _ => by positivity) f K hK
      _ = ENNReal.ofReal (Real.exp beta) / K := by
        rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.2 hK)]
        simp
  · change Measure.map (extendBoxCurrent d n)
      ((sourcelessCurrentPMF (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) hbeta (fun _ => by positivity)).toMeasure) {m | K ≤ m e} ≤ _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K ≤ m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
    have hempty : extendBoxCurrent d n ⁻¹'
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K ≤ m e} = ∅ := by
      ext m
      simp [extendBoxCurrent_outside d n m e he, Nat.not_le_of_lt hK]
    rw [hempty, measure_empty]
    exact bot_le



theorem freeBoxCurrentMeasure_tight (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsTightMeasureSet (Set.range fun n =>
      (freeBoxCurrentMeasure d n beta hbeta :
        Measure (InfiniteCurrentConfig (Sym2 (Site d))))) := by
  exact isTightMeasureSet_range_of_uniform_inverse_tail
    (fun n => freeBoxCurrentMeasure d n beta hbeta)
    (ENNReal.ofReal (Real.exp beta)) ENNReal.ofReal_ne_top
    (fun n e K hK =>
      freeBoxCurrentMeasure_edge_inverse_tail_le d n beta hbeta e K hK)


theorem freeBoxCurrentMeasure_subsequence
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu := by
  exact weakCurrent_subsequence_of_tight
    (fun n => freeBoxCurrentMeasure d n beta hbeta)
    (freeBoxCurrentMeasure_tight d beta hbeta)



theorem freeBoxCurrentMeasure_subsequence_with_cylinders
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nu ∧
        ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)),
          Tendsto
            (fun k => freeBoxCurrentMeasure d (phi k) beta hbeta
              (currentCylinder S A)) atTop
            (nhds (nu (currentCylinder S A))) := by
  obtain ⟨nu, phi, hphi, hlim⟩ :=
    freeBoxCurrentMeasure_subsequence d beta hbeta
  exact ⟨nu, phi, hphi, hlim, fun S A => hlim.cylinder S A⟩

end StatMech.FrontierB
