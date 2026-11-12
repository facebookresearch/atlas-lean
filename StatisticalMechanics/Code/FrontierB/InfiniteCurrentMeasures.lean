/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.InfiniteCurrentPairCylinders

open Filter MeasureTheory

namespace StatMech.FrontierB

open Lattice

structure FreePlusCurrentLimitData (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) where
  freeLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  plusLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  free_tendsto : WeakCurrentConverges
    ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ subsequence) freeLimit
  plus_tendsto : WeakCurrentConverges
    ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ subsequence) plusLimit

noncomputable def freePlusCurrentLimitData
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    FreePlusCurrentLimitData d beta hbeta := by
  exact Classical.choice (show Nonempty (FreePlusCurrentLimitData d beta hbeta) from by
    obtain ⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩ :=
      freePlusBoxCurrentMeasure_joint_subsequence d beta hbeta
    exact ⟨⟨nuFree, nuPlus, phi, hphi, hfree, hplus⟩⟩)

noncomputable def infiniteFreeCurrentMeasure
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (freePlusCurrentLimitData d beta hbeta).freeLimit

noncomputable def infinitePlusCurrentMeasure
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))) :=
  (freePlusCurrentLimitData d beta hbeta).plusLimit

noncomputable def infiniteCurrentBoxSubsequence
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) : ℕ → ℕ :=
  (freePlusCurrentLimitData d beta hbeta).subsequence

theorem infiniteCurrentBoxSubsequence_strictMono
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    StrictMono (infiniteCurrentBoxSubsequence d beta hbeta) :=
  (freePlusCurrentLimitData d beta hbeta).strictMono_subsequence

theorem freeBoxCurrentMeasure_tendsto_infiniteFree
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    WeakCurrentConverges
      ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘
        infiniteCurrentBoxSubsequence d beta hbeta)
      (infiniteFreeCurrentMeasure d beta hbeta) :=
  (freePlusCurrentLimitData d beta hbeta).free_tendsto

theorem plusBoxCurrentMeasure_tendsto_infinitePlus
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    WeakCurrentConverges
      ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘
        infiniteCurrentBoxSubsequence d beta hbeta)
      (infinitePlusCurrentMeasure d beta hbeta) :=
  (freePlusCurrentLimitData d beta hbeta).plus_tendsto

theorem freeBoxCurrentMeasure_cylinder_tendsto_infiniteFree
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun k => freeBoxCurrentMeasure d
        (infiniteCurrentBoxSubsequence d beta hbeta k) beta hbeta
        (currentCylinder S A)) atTop
      (nhds (infiniteFreeCurrentMeasure d beta hbeta
        (currentCylinder S A))) :=
  (freeBoxCurrentMeasure_tendsto_infiniteFree d beta hbeta).cylinder S A

theorem plusBoxCurrentMeasure_cylinder_tendsto_infinitePlus
    (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)) :
    Tendsto
      (fun k => plusBoxCurrentMeasure d
        (infiniteCurrentBoxSubsequence d beta hbeta k) beta hbeta
        (currentCylinder S A)) atTop
      (nhds (infinitePlusCurrentMeasure d beta hbeta
        (currentCylinder S A))) :=
  (plusBoxCurrentMeasure_tendsto_infinitePlus d beta hbeta).cylinder S A

end StatMech.FrontierB

