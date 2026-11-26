/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.EndpointMapMultigraph.SpectralApproximation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace EndpointMapMultigraphSpectralApproximationTest

open EndpointMapMultigraph Matrix

private def half : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by constructor <;> norm_num⟩

-- Two parallel unit edges versus a single unit edge in the opposite orientation.
private def parallelPair : WeightedPresentation (Fin 2) (Fin 2) :=
  ⟨fun _ => 0, fun _ => 1, fun _ => 1, fun _ => zero_le_one⟩

private def singleEdge : WeightedPresentation (Fin 2) Unit :=
  ⟨fun _ => 1, fun _ => 0, fun _ => 1, fun _ => zero_le_one⟩

private theorem single_approximates_pair : singleEdge.IsSpectralApproximation parallelPair half := by
  intro x
  simp only [dotProduct_mulVec_laplacian, parallelPair, singleEdge, half, Fin.sum_univ_two,
    Fintype.sum_unique, one_mul]
  constructor <;> nlinarith [sq_nonneg (x 0 - x 1)]

example : singleEdge.IsCutApproximation parallelPair half :=
  single_approximates_pair.isCutApproximation

-- At {0}, the cut weights are 2 and 1. The forward lower bound is tight, but swapping
-- the graphs would require 2 ≤ 3/2.
example : ¬ parallelPair.IsCutApproximation singleEdge half := by
  intro h
  have upper := (h {0}).2
  norm_num [cut, Finset.sum_filter, parallelPair, singleEdge, half, Fin.sum_univ_two] at upper

-- The edge order in the triangle is 01, 02, 12.
private def triangle (w : Fin 3 → ℝ) (hw : 0 ≤ w) : WeightedPresentation (Fin 3) (Fin 3) :=
  ⟨![0, 0, 1], ![1, 2, 2], w, hw⟩

private def unitTriangle := triangle (fun _ => 1) fun _ => zero_le_one

private def pathInTriangle := triangle ![2, 0, 1] (by intro i; fin_cases i <;> norm_num)

-- Every cut is within the prescribed factors, even where an original edge now has weight zero.
example : pathInTriangle.IsCutApproximation unitTriangle half := by
  intro S
  simp only [unitTriangle, pathInTriangle, triangle, half, cut, Finset.sum_filter,
    Fin.sum_univ_three]
  by_cases h₀ : 0 ∈ S <;> by_cases h₁ : 1 ∈ S <;> by_cases h₂ : 2 ∈ S <;>
    norm_num [h₀, h₁, h₂]

-- The potential (2, -1, 1) is not a cut indicator. Its energies 14 and 22 violate 22 ≤ 21.
example : ¬ pathInTriangle.IsSpectralApproximation unitTriangle half := by
  intro h
  have upper := (h ![2, -1, 1]).2
  norm_num [dotProduct_mulVec_laplacian, unitTriangle, pathInTriangle, triangle, half,
    Fin.sum_univ_three] at upper

end EndpointMapMultigraphSpectralApproximationTest
