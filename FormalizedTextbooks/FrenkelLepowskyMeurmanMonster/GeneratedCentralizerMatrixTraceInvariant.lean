/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Intrinsic recovery of the matrix trace from the actual algebra identity. -/
module
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GriessUnit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerPlusCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCentralizerTensor

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- Pairing with the actual algebra identity measures one quarter of the matrix trace. -/
theorem generatedCentral_unit_pairing_trace (x : GriessSpace) :
    griessForm griessUnit x = (griessConwayEncode x).1.trace / 4 := by
  rw [griessForm_eq_conwayRawForm, griessUnit_encode]
  simp only [conwayRawForm, conwayMatrixForm_eq_sum, Matrix.diagonal_apply,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, map_zero, LinearMap.zero_apply, add_zero]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [Matrix.trace, Matrix.diag_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every actual generated-group element preserves the encoded symmetric matrix trace. -/
theorem generated_group_preserves_encoded_matrix_trace (g : G) (x : GriessSpace) :
    (griessConwayEncode (g.val x)).1.trace = (griessConwayEncode x).1.trace := by
  have h := generated_group_unit_pairing g x
  rw [generatedCentral_unit_pairing_trace, generatedCentral_unit_pairing_trace] at h
  linarith

/-- In particular the full centralizer preserves the matrix trace on its fixed space. -/
theorem generatedCentralizer_preserves_matrix_trace (g : generatedCentralizer)
    (x : generatedCentralPlus) :
    (generatedCentralPlusCoordinates (generatedCentralizerPlusEquiv g x)).1.val.trace =
      (generatedCentralPlusCoordinates x).1.val.trace := by
  exact generated_group_preserves_encoded_matrix_trace g.val x.val

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
