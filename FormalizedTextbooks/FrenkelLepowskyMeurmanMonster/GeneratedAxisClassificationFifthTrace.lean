/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthTrace

/-! The fifth candidate lies in a new actual H axis orbit, by its original matrix invariant. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators

/-- The actual fifth watermark has matrix-square trace three. -/
theorem generatedFifth_matrix_square_trace :
    generatedFourthMatrixSquareTrace generatedFifthAxis = 3 := by
  unfold generatedFourthMatrixSquareTrace
  have hm : (griessConwayEncode generatedFifthAxis).1 =
      Matrix.diagonal (fun i : Fin 24 => (generatedFifthProjectionDiagonal i : ℝ) / 16) := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq, generatedFifth_matrix_diagonal]
    · rw [Matrix.diagonal_apply_ne _ hij, generatedFifth_matrix_off_diagonal i j hij]
  rw [hm, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  norm_num [generatedFifthProjectionDiagonal, Fin.sum_univ_succ]

/-- No actual signed-short axis can be transported locally to the fifth candidate. -/
theorem generatedFifth_not_local_short (h : H) (r : GriessShortIndex) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis r c) ≠ generatedFifthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h (conwayShortAxis r c)
  rw [he, generatedFifth_matrix_square_trace, generatedFourth_matrix_square_trace_short] at ht
  norm_num at ht

/-- No actual octad-image axis can be transported locally to the fifth candidate. -/
theorem generatedFifth_not_local_octad (h : H) (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)) ≠ generatedFifthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))
  rw [he, generatedFifth_matrix_square_trace, generatedFourth_matrix_square_trace_octad] at ht
  norm_num at ht

/-- No actual odd-image axis can be transported locally to the fifth candidate. -/
theorem generatedFifth_not_local_odd (h : H) (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c)) ≠ generatedFifthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h
    (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))
  rw [he, generatedFifth_matrix_square_trace, generatedFourth_matrix_square_trace_odd] at ht
  norm_num at ht

/-- No actual fourth-orbit axis can be transported locally to the fifth candidate. -/
theorem generatedFifth_not_local_fourth (h : H) :
    rhoLocal h generatedFourthAxis ≠ generatedFifthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h generatedFourthAxis
  rw [he, generatedFifth_matrix_square_trace, generatedFourth_matrix_square_trace] at ht
  norm_num at ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
