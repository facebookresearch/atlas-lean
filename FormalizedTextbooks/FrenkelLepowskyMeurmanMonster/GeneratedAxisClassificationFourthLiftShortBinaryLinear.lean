/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortMatrixAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFourthLiftShortMatrixPhase

/-! Sparse evaluation of the certified actual extraspecial binary matrix. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped Matrix BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Nonzero columns of each row of the genuine certified binary matrix. -/
def generatedFourthLiftShortBinaryRows : Fin 24 → Finset (Fin 24) :=
  ![{7, 13, 14, 15, 23},
    {5, 9, 12, 14, 15},
    {4, 8, 9, 12, 13, 15},
    {4, 5, 8, 12, 13, 14},
    {4, 10, 23},
    {5},
    {6, 10},
    {7},
    {8},
    {9},
    {23},
    {2, 3, 5, 7, 9, 13, 16, 18, 22, 23},
    {1, 2, 3, 5, 10, 12, 23},
    {0, 2, 3, 5, 7, 9, 13, 23},
    {0, 1, 3, 5, 6, 7, 8, 10, 14, 23},
    {0, 1, 2, 5, 6, 8, 9, 10, 15, 23},
    {2, 3, 5, 9, 14, 15, 16},
    {1, 3, 4, 7, 8, 9, 12, 14, 17, 23},
    {5, 14, 15, 18},
    {1, 2, 3, 4, 5, 9, 12, 13, 14, 19},
    {2, 3, 7, 20},
    {1, 2, 5, 6, 7, 9, 10, 14, 15, 21},
    {1, 2, 3, 11, 18, 22},
    {10, 23}]

/-- Sum only the nonzero original binary-matrix coefficients. -/
def generatedFourthLiftShortBinaryLinear : Module.End (ZMod 2) (Fin 24 → ZMod 2) where
  toFun v i := ∑ j ∈ generatedFourthLiftShortBinaryRows i, v j
  map_add' u v := by
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

/-- All 576 sparse binary coefficients equal the already certified original matrix entries. -/
theorem generatedFourth_lift_short_binary_rows_certificate :
    ∀ i j : Fin 24, generatedFourthLiftShortBinaryLinear (Pi.single j 1) i =
      generatedFourthLiftQBinaryMatrix i j := by
  decide +kernel

/-- Sparse evaluation is exactly the actual binary matrix on every vector. -/
theorem generatedFourth_lift_short_binary_linear (v : Fin 24 → ZMod 2) :
    generatedFourthLiftQBinaryMatrix *ᵥ v = generatedFourthLiftShortBinaryLinear v := by
  have h : Matrix.toLin' generatedFourthLiftQBinaryMatrix =
      generatedFourthLiftShortBinaryLinear := by
    apply (Pi.basisFun (ZMod 2) (Fin 24)).ext
    intro j
    ext i
    simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one,
      Matrix.col_apply]
    exact (generatedFourth_lift_short_binary_rows_certificate i j).symm
  exact DFunLike.congr_fun h v

/-- Complete actual Q evaluation using sparse binary and full central-phase coefficients. -/
def generatedFourthLiftShortMatrixSparse (q : Q) : Q :=
  ⟨ofAdd (generatedFourthLiftShortBinaryLinear (toAdd q.base)),
    ofAdd (toAdd q.coeff + generatedFourthLiftQPhaseFast (toAdd q.base))⟩

/-- Sparse evaluation equals the genuine corrected full-Q conjugation everywhere. -/
theorem generatedFourth_lift_short_matrix_sparse (q : Q) :
    spinConjugation generatedFourthFlagCorrectedLift.val.1 q =
      generatedFourthLiftShortMatrixSparse q := by
  rw [generatedFourth_lift_short_matrix_action, generatedFourth_lift_short_matrix_value,
    generatedFourth_lift_q_phase_fast, generatedFourth_lift_short_binary_linear]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
