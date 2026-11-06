/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagRecognition

/-! A genuine conjugation invariant distinguishing the fourth flag matrix. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Genuine local matrix transport preserves the trace of the matrix square. -/
theorem generatedAxisE8Short_trace_square_action (g : leechIsomSubgroup)
    (A : Matrix (Fin 24) (Fin 24) ℝ) :
    Matrix.trace (conwayMatrixAction g A * conwayMatrixAction g A) =
      Matrix.trace (A * A) := by
  rw [← conwayMatrixAction_mul, conwayMatrixAction_trace]

/-- The flag watermark has trace eight in the physical normalization. -/
theorem generatedAxisE8ShortFlagMatrix_trace (P U : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : Matrix.trace P = 8) (hU : Matrix.trace U = 4) :
    Matrix.trace (generatedAxisE8ShortFlagMatrix P U) = 8 := by
  simp only [generatedAxisE8ShortFlagMatrix, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul, hP, hU]
  norm_num

/-- The squared flag matrix has trace 29/8, retaining all physical coefficients. -/
theorem generatedAxisE8ShortFlagMatrix_trace_square
    (P U : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : P * P = P) (hU : U * U = (4 : ℝ) • U)
    (hPU : P * U = U) (hUP : U * P = U)
    (htP : Matrix.trace P = 8) (htU : Matrix.trace U = 4) :
    Matrix.trace (generatedAxisE8ShortFlagMatrix P U *
      generatedAxisE8ShortFlagMatrix P U) = 29 / 8 := by
  simp only [generatedAxisE8ShortFlagMatrix, add_mul, mul_add, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul, Matrix.one_mul, Matrix.mul_one,
    hP, hU, hPU, hUP, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul, htP, htU]
  norm_num

/-- The actual coordinate E8 projection has trace eight. -/
theorem generatedAxisE8ShortProjection_trace (o : Fin 759) :
    Matrix.trace (generatedAxisE8ShortProjection o) = 8 := by
  rw [generatedAxisE8ShortProjection, Matrix.trace_diagonal]
  have hv (a : ZMod 2) : (if a = 0 then (0 : ℝ) else 1) = (a.val : ℝ) := by
    fin_cases a <;> norm_num [show (1 : ZMod 2).val = 1 by decide]
  simp_rw [hv]
  exact_mod_cast golayOctadWord_weight o

/-- The actual short outer matrix has trace four. -/
theorem generatedAxisE8ShortOuter_trace (r : GriessShortIndex) :
    Matrix.trace (generatedAxisE8ShortOuter r) = 4 := by
  rw [generatedAxisE8ShortOuter, Matrix.trace_vecMulVec]
  exact griessShortVector_norm_sq r

/-- Every actual incident E8 short-line flag has squared matrix trace 29/8. -/
theorem generatedAxisE8ShortFlagMatrix_actual_trace_square (o : Fin 759)
    (r : GriessShortIndex) (hr : r ∈ generatedAxisE8ShortLines
      (generatedAxisE8CoordinateSection (golayOctadWord o))) :
    Matrix.trace (generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection o) (generatedAxisE8ShortOuter r) *
      generatedAxisE8ShortFlagMatrix
        (generatedAxisE8ShortProjection o) (generatedAxisE8ShortOuter r)) = 29 / 8 :=
  generatedAxisE8ShortFlagMatrix_trace_square _ _
    (generatedAxisE8ShortProjection_square o) (generatedAxisE8ShortOuter_square r)
    (generatedAxisE8ShortProjection_mul_outer o r hr)
    (generatedAxisE8ShortOuter_mul_projection o r hr)
    (generatedAxisE8ShortProjection_trace o) (generatedAxisE8ShortOuter_trace r)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
