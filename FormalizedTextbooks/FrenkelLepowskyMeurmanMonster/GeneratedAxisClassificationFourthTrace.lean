/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthRecognition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagTrace
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOddCoordinates

/-! The actual fourth representative belongs to a fourth distinct genuine local axis orbit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A matrix-square trace invariant evaluated on the original Griess coordinates. -/
def generatedFourthMatrixSquareTrace (x : GriessSpace) : ℝ :=
  Matrix.trace ((griessConwayEncode x).1 * (griessConwayEncode x).1)

/-- Every genuine local H element preserves the original matrix-square trace. -/
theorem generatedFourth_matrix_square_trace_local (h : H) (x : GriessSpace) :
    generatedFourthMatrixSquareTrace (rhoLocal h x) = generatedFourthMatrixSquareTrace x := by
  obtain ⟨f, hf⟩ := QuotientGroup.mk'_surjective localDiagonalSubgroup h
  change localFiberIntoH f = h at hf
  rw [← hf]
  change generatedFourthMatrixSquareTrace (localGriessRepresentation f x) = _
  simp only [generatedFourthMatrixSquareTrace, localGriessRepresentation_encode,
    localConwayRawRepresentation_apply]
  exact generatedAxisE8Short_trace_square_action f.val.2 _

/-- The actual fourth flag watermark has square trace 29/8. -/
theorem generatedFourth_matrix_square_trace :
    generatedFourthMatrixSquareTrace generatedFourthAxis = 29 / 8 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedFourth_matrix_actual_flag]
  exact generatedAxisE8ShortFlagMatrix_actual_trace_square _ _ generatedFourth_flag_incident

/-- Every signed short axis has matrix-square trace 64 in the actual normalization. -/
theorem generatedFourth_matrix_square_trace_short (r : GriessShortIndex) (c : ZMod 2) :
    generatedFourthMatrixSquareTrace (conwayShortAxis r c) = 64 := by
  rw [generatedFourthMatrixSquareTrace, conwayShortAxis_encode]
  change Matrix.trace (((2 : ℝ) • generatedAxisE8ShortOuter r) *
    ((2 : ℝ) • generatedAxisE8ShortOuter r)) = 64
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, generatedAxisE8ShortOuter_square,
    Matrix.trace_smul, Matrix.trace_smul, generatedAxisE8ShortOuter_trace]
  norm_num

/-- Every original octad triality image has matrix-square trace eight. -/
theorem generatedFourth_matrix_square_trace_octad (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    generatedFourthMatrixSquareTrace
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)) = 8 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedAxis_triality_octad_matrix, Matrix.diagonal_mul_diagonal]
  have he : (fun i : Fin 24 =>
      (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then (1 : ℝ) else 0) *
      (if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then (1 : ℝ) else 0)) =
      (fun i : Fin 24 =>
        if (golayEncodedMask (golayOctadLabel o).val).testBit i.val then (1 : ℝ) else 0) := by
    funext i
    split_ifs <;> norm_num
  rw [he]
  exact (generatedAxis_triality_octad_matrix o e c) ▸
    generatedAxis_triality_octad_matrix_trace o e c

/-- Every original odd triality image has matrix-square trace 13/2. -/
theorem generatedFourth_matrix_square_trace_odd (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    generatedFourthMatrixSquareTrace
      (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c)) = 13 / 2 := by
  unfold generatedFourthMatrixSquareTrace
  rw [generatedAxis_triality_odd_matrix, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have he (j : Fin 24) :
      (1 / 4 + if j = i then (2 : ℝ) else 0) *
        (1 / 4 + if j = i then (2 : ℝ) else 0) =
          1 / 16 + if j = i then (5 : ℝ) else 0 := by
    by_cases hj : j = i <;> norm_num [hj]
  simp_rw [he]
  norm_num [Finset.sum_add_distrib]

/-- The genuine fourth axis cannot be transported locally from any signed short axis. -/
theorem generatedFourth_not_local_short (h : H) (r : GriessShortIndex) (c : ZMod 2) :
    rhoLocal h (conwayShortAxis r c) ≠ generatedFourthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h (conwayShortAxis r c)
  rw [he, generatedFourth_matrix_square_trace, generatedFourth_matrix_square_trace_short] at ht
  norm_num at ht

/-- The genuine fourth axis cannot be transported locally from any octad triality image. -/
theorem generatedFourth_not_local_octad (h : H) (o : Fin 759) (e : Fin 64) (c : ZMod 2) :
    rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)) ≠
      generatedFourthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h
    (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c))
  rw [he, generatedFourth_matrix_square_trace, generatedFourth_matrix_square_trace_octad] at ht
  norm_num at ht

/-- The genuine fourth axis cannot be transported locally from any odd triality image. -/
theorem generatedFourth_not_local_odd (h : H) (d : Fin 2048) (i : Fin 24) (c : ZMod 2) :
    rhoLocal h (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c)) ≠
      generatedFourthAxis := by
  intro he
  have ht := generatedFourth_matrix_square_trace_local h
    (sExtra (conwayShortAxis (Sum.inr (Sum.inr (d, i))) c))
  rw [he, generatedFourth_matrix_square_trace, generatedFourth_matrix_square_trace_odd] at ht
  norm_num at ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
