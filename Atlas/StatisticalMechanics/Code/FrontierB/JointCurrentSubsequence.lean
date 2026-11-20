/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.FreeCurrentLimit
import Code.FrontierB.PlusCurrentLimit

open Filter MeasureTheory
open scoped ENNReal

namespace StatMech.FrontierB

open Lattice

theorem freePlusBoxCurrentMeasure_joint_subsequence
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ (nuFree nuPlus : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nuFree ∧
        WeakCurrentConverges
          ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nuPlus := by
  obtain ⟨nuFree, phiFree, hphiFree, hfree⟩ :=
    freeBoxCurrentMeasure_subsequence d beta hbeta
  obtain ⟨nuPlus, phiPlus, hphiPlus, hplus⟩ :=
    weakCurrent_subsequence_of_uniform_inverse_tail
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phiFree)
      (ENNReal.ofReal (Real.exp beta)) ENNReal.ofReal_ne_top
      (fun i e K hK =>
        plusBoxCurrentMeasure_edge_inverse_tail_le
          d (phiFree i) beta hbeta e K hK)
  refine ⟨nuFree, nuPlus, phiFree ∘ phiPlus,
    hphiFree.comp hphiPlus, ?_, hplus⟩
  exact hfree.comp hphiPlus.tendsto_atTop

theorem freePlusBoxCurrentMeasure_joint_subsequence_with_cylinders
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ∃ (nuFree nuPlus : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ phi) nuFree ∧
        WeakCurrentConverges
          ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ phi) nuPlus ∧
        ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)),
          Tendsto
            (fun k => freeBoxCurrentMeasure d (phi k) beta hbeta
              (currentCylinder S A)) atTop
            (nhds (nuFree (currentCylinder S A))) ∧
          Tendsto
            (fun k => plusBoxCurrentMeasure d (phi k) beta hbeta
              (currentCylinder S A)) atTop
            (nhds (nuPlus (currentCylinder S A))) := by
  obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
    freePlusBoxCurrentMeasure_joint_subsequence d beta hbeta
  exact ⟨nuFree, nuPlus, phi, hphi, hfree, hplus,
    fun S A => ⟨hfree.cylinder S A, hplus.cylinder S A⟩⟩

end StatMech.FrontierB

