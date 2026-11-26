/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.DiscreteLogConcaveSelfConvolution
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum

/-!
# Reeve tetrahedron convolution regression

Compute the convolution at the two lattice endpoints and their missing midpoint.
-/

open MathlibExt.Probability.DiscreteLogConcaveSelfConvolutionOWR14298808Problem013Wanted

private def vertices : Finset (Fin 3 → ℤ) :=
  {![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 2]}

private noncomputable def mass (x : Fin 3 → ℤ) : ℝ := if x ∈ vertices then 1 / 4 else 0

private lemma convolution_eq_vertices_sum (z : Fin 3 → ℤ) :
    selfConvolution mass z = ∑ x ∈ vertices, (1 / 4 : ℝ) * mass (z - x) := by
  rw [selfConvolution_eq_tsum]
  rw [tsum_eq_sum (s := vertices) (fun x hx => by simp [mass, hx])]
  exact Finset.sum_congr rfl fun x hx => by simp [mass, hx]

example : selfConvolution mass ![1, 1, 0] = 1 / 8 ∧
    selfConvolution mass ![1, 1, 2] = 1 / 8 ∧ selfConvolution mass ![1, 1, 1] = 0 := by
  have h₀ : (![0, 0, 0] : Fin 3 → ℤ) ∉
      ({![1, 0, 0], ![0, 1, 0], ![1, 1, 2]} : Finset (Fin 3 → ℤ)) := by decide
  have h₁ : (![1, 0, 0] : Fin 3 → ℤ) ∉
      ({![0, 1, 0], ![1, 1, 2]} : Finset (Fin 3 → ℤ)) := by decide
  have h₂ : (![0, 1, 0] : Fin 3 → ℤ) ∉ ({![1, 1, 2]} : Finset (Fin 3 → ℤ)) := by decide
  simp only [convolution_eq_vertices_sum, vertices, Finset.sum_insert h₀,
    Finset.sum_insert h₁, Finset.sum_insert h₂, Finset.sum_singleton]
  simp (disch := decide) only [mass, ite_eq_left, ite_eq_right]
  norm_num

example : ¬ selfConvolutionPreservesLogConcavity :=
  selfConvolutionPreservesLogConcavity_refuted
