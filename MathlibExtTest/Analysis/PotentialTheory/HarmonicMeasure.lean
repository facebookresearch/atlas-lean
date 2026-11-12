/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Leonard Dinh
-/
module

public import MathlibExt.Analysis.PotentialTheory.HarmonicMeasure

@[expose] public section

namespace MathlibExtTest.Analysis.PotentialTheory.HarmonicMeasure

open MetaMathlibExt

-- Analysis 370: Superharmonic On A Set

theorem IsSuperharmonicOn.lowerSemicontinuousOn
    {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (h : IsSuperharmonicOn u Ω) :
    LowerSemicontinuousOn u Ω := by
  exact h.1

-- Analysis 371: Upper Perron Solution

theorem upperPerronSolution_congr
    {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (h : f = g) :
    upperPerronSolution Ω f x =
      upperPerronSolution Ω g x := by
  subst g
  rfl

theorem ereal_sInf_empty :
    sInf (∅ : Set EReal) = ⊤ := by
  simp

-- Analysis 372: Harmonic Measure

theorem IsHarmonicMeasure.measure_compl_frontier_eq_zero
    {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {x : EuclideanSpace ℝ (Fin n)}
    {μ : MeasureTheory.ProbabilityMeasure
      (EuclideanSpace ℝ (Fin n))}
    (h : IsHarmonicMeasure Ω x μ) :
    (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
        ((frontier Ω)ᶜ) = 0 := by
  rcases h with ⟨_, _, _, _, hfrontier, _⟩
  exact hfrontier

end MathlibExtTest.Analysis.PotentialTheory.HarmonicMeasure

end
