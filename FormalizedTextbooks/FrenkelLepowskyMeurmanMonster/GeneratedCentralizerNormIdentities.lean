/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The exact norm coefficients that separate the actual fixed-space constituents. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTraceFormula
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerMatrixTraceInvariant

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem realSquareNorm_zero {ι : Type*} [Fintype ι] (X : ι → ℝ) :
    (∑ r, X r ^ 2) = 0 ↔ X = 0 := by
  constructor
  · intro h
    funext r
    exact (Finset.sum_sq_eq_zero_iff _ _).mp h r (Finset.mem_univ r)
  · intro h
    simp only [h, Pi.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]

/-- Squared ordinary Frobenius norm of the actual symmetric matrix coordinate. -/
noncomputable def generatedCentralMatrixNormSq (x : generatedCentralPlus) : ℝ :=
  ∑ i, ∑ j, (generatedCentralPlusCoordinates x).1.val i j ^ 2

/-- Squared ordinary Euclidean norm of the actual short-vector coordinate. -/
noncomputable def generatedCentralShortNormSq (x : generatedCentralPlus) : ℝ :=
  ∑ r, (generatedCentralPlusCoordinates x).2 r ^ 2

/-- The actual fixed-space norm is the sum of its two coordinate square norms. -/
theorem generatedCentralPlus_form_self (x : generatedCentralPlus) :
    griessForm x.val x.val = generatedCentralMatrixNormSq x + generatedCentralShortNormSq x := by
  rw [generatedCentralPlus_griessForm_coordinates]
  simp only [generatedCentralMatrixNormSq, generatedCentralShortNormSq, pow_two]

/-- The short-coordinate square norm vanishes exactly on the actual matrix constituent. -/
theorem generatedCentralShortNormSq_eq_zero_iff (x : generatedCentralPlus) :
    generatedCentralShortNormSq x = 0 ↔ x ∈ generatedCentralMatrix := by
  rw [mem_generatedCentralMatrix]
  change (∑ r, (generatedCentralPlusCoordinates x).2 r ^ 2) = 0 ↔
    (generatedCentralPlusCoordinates x).2 = 0
  exact realSquareNorm_zero _

/-- The matrix-coordinate square norm vanishes exactly on the actual short constituent. -/
theorem generatedCentralMatrixNormSq_eq_zero_iff (x : generatedCentralPlus) :
    generatedCentralMatrixNormSq x = 0 ↔ x ∈ generatedCentralShort := by
  rw [mem_generatedCentralShort]
  constructor
  · intro h
    apply Subtype.ext
    funext i j
    have hn : ∀ i : Fin 24, 0 ≤ ∑ j, (generatedCentralPlusCoordinates x).1.val i j ^ 2 :=
      fun i => Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)).mp h i
      (Finset.mem_univ i)
    exact (Finset.sum_sq_eq_zero_iff _ _).mp hi j (Finset.mem_univ j)
  · intro h
    simp only [generatedCentralMatrixNormSq, h, Submodule.coe_zero, Matrix.zero_apply,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero]

/-- A real symmetric matrix's trace square is its Frobenius square norm. -/
theorem generatedCentral_symmetric_trace_square (A : Sym24) :
    (A.val.transpose * A.val.transpose).trace = ∑ i, ∑ j, A.val i j ^ 2 := by
  rw [A.property]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : A.val j i = A.val i j :=
    congrArg (fun B : Matrix (Fin 24) (Fin 24) ℝ => B i j) A.property
  rw [hs, pow_two]

/-- The physical trace coefficients are 4096, 2560 and 4608 on the fixed-space coordinates. -/
theorem generatedCentral_coordinate_trace_norm (x : generatedCentralPlus) :
    LinearMap.trace ℝ _
      ((centralizerCoordinateTensorMul (generatedCentralPlusCoordinates x).1.val
        (generatedCentralPlusCoordinates x).2).comp
       (centralizerCoordinateTensorMul (generatedCentralPlusCoordinates x).1.val
        (generatedCentralPlusCoordinates x).2)) =
      4096 * generatedCentralMatrixNormSq x +
      2560 * ((generatedCentralPlusCoordinates x).1.val.trace) ^ 2 +
      4608 * generatedCentralShortNormSq x := by
  rw [centralizerCoordinateTensorMul_trace_comp, generatedCentral_symmetric_trace_square]
  simp only [generatedCentralMatrixNormSq, generatedCentralShortNormSq, pow_two]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
