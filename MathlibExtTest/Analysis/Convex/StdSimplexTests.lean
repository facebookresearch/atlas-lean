/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.StdSimplexWeights

/-!
# Tests for StdSimplex composition, products, and faces

* `sigma`/`prod` coordinate formulas on concrete `Fin 2` points, and the
  `iConvexComb` coordinate sum.
* Support factorization: mapping a strictly positive point along
  `Fin.succAbove` has range exactly the nonzero coordinates.
* Face factorization: a point with a zero coordinate factors through the
  corresponding face, with the expected remaining coordinates.
* The face inclusion is a closed embedding, and the simplex map along an
  injective coordinate map is injective.
-/

namespace MathlibExtTest.StdSimplex

open Convexity StdSimplex

/-- The `(3/4, 1/4)` point on `Fin 2`. -/
noncomputable def w34 : StdSimplex ℝ (Fin 2) :=
  ofWeights ![3 / 4, 1 / 4] (by intro i; fin_cases i <;> norm_num) (by
    norm_num [Fin.sum_univ_two])

/-- The `(1/3, 2/3)` point on `Fin 2`. -/
noncomputable def w13 : StdSimplex ℝ (Fin 2) :=
  ofWeights ![1 / 3, 2 / 3] (by intro i; fin_cases i <;> norm_num) (by
    norm_num [Fin.sum_univ_two])

/-- The uniform `(1/2, 1/2)` point on `Fin 2`. -/
noncomputable def w12 : StdSimplex ℝ (Fin 2) :=
  ofWeights ![1 / 2, 1 / 2] (by intro i; fin_cases i <;> norm_num) (by
    norm_num [Fin.sum_univ_two])

/-- The `(1/2, 0, 1/2)` point on `Fin 3`, with a zero middle coordinate. -/
noncomputable def w102 : StdSimplex ℝ (Fin 3) :=
  ofWeights ![1 / 2, 0, 1 / 2] (by intro i; fin_cases i <;> norm_num) (by
    norm_num [Fin.sum_univ_three])

example : (prod w34 w13).weights (0, 1) = 1 / 2 := by
  have h0 : w34.weights 0 = 3 / 4 := by simp [w34]
  have h1 : w13.weights 1 = 2 / 3 := by simp [w13]
  rw [prod_apply, h0, h1]
  norm_num

example : (sigma w34 (fun _ : Fin 2 => w13)).weights ⟨1, 0⟩ = 1 / 12 := by
  have h1 : w34.weights 1 = 1 / 4 := by simp [w34]
  have h0 : w13.weights 0 = 1 / 3 := by simp [w13]
  rw [sigma_apply]
  dsimp only
  rw [h1, h0]
  norm_num

example : (w34.iConvexComb (fun _ : Fin 2 => w13)).weights 1 = 2 / 3 := by
  have h0 : w34.weights 0 = 3 / 4 := by simp [w34]
  have h1 : w34.weights 1 = 1 / 4 := by simp [w34]
  have h2 : w13.weights 1 = 2 / 3 := by simp [w13]
  rw [weights_iConvexComb_apply, Fin.sum_univ_two, h0, h1, h2]
  norm_num

example :
    Set.range (Fin.succAbove (0 : Fin 3) : Fin 2 → Fin 3)
      = {i | (w12.map (Fin.succAbove (0 : Fin 3))).weights i ≠ 0} := by
  have hq_pos : ∀ i, 0 < w12.weights i := by
    intro i
    fin_cases i <;> simp [w12]
  exact range_eq_support_of_map_strictly_positive hq_pos

example : ∃ q : StdSimplex ℝ (Fin 2),
    StdSimplex.map (Fin.succAbove (1 : Fin 3)) q = w102 ∧ q.weights 0 = 1 / 2 ∧
      q.weights 1 = 1 / 2 := by
  have hj : w102.weights 1 = 0 := by simp [w102]
  obtain ⟨q, hq⟩ := face_factor_succAbove w102 1 hj
  have hcoord : ∀ k : Fin 2,
      q.weights k = w102.weights (Fin.succAbove (1 : Fin 3) k) := by
    intro k
    have h2 := congrArg StdSimplex.weights hq
    have h3 : (StdSimplex.map (Fin.succAbove (1 : Fin 3)) q).weights
        (Fin.succAbove (1 : Fin 3) k) = q.weights k := by
      rw [weights_map]
      exact Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective _ _
    rw [h2] at h3
    exact h3.symm
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hcoord 0]
    simp [w102]
  · rw [hcoord 1]
    simp [w102]

open Topology in
example (j : Fin 3) :
    IsClosedEmbedding
      (StdSimplex.map (R := ℝ) (Fin.succAbove j : Fin 2 → Fin 3)) :=
  isClosedEmbedding_map_succAbove j

example (j : Fin 3) :
    Function.Injective
      (StdSimplex.map (R := ℝ) (Fin.succAbove j : Fin 2 → Fin 3)) :=
  map_injective Fin.succAbove_right_injective

end MathlibExtTest.StdSimplex
