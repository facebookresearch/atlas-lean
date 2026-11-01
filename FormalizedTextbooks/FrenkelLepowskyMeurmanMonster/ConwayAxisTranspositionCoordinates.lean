/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisMatrixTranspositionCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.ConwayAxisTensorTransposition

/-! The actual rank-one form and tensor rows needed for the full axis transposition. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The rank-one coefficient in the transposition formula is the actual full
Conway form against the actual axis, rather than an independently supplied scalar. -/
theorem conwayShortAxisRaw_form (r : GriessShortIndex) (c : ZMod 2) (U : ConwayRawSpace) :
    conwayRawForm (conwayShortAxisRaw r c) U =
      2 * axisMatrixContraction (griessShortVector r) U.1 - 8 * qSign c * U.2.1 r := by
  have hm : conwayMatrixForm (conwayShortAxisRaw r c).1 U.1 =
      2 * axisMatrixContraction (griessShortVector r) U.1 := by
    rw [conwayMatrixForm_eq_sum]
    simp only [conwayShortAxisRaw, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      axisMatrixContraction, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : (∑ a, (conwayShortAxisRaw r c).2.1 a * U.2.1 a) =
      (-8 * qSign c) * U.2.1 r := by
    classical
    rw [Finset.sum_eq_single r]
    · simp [conwayShortAxisRaw]
    · intro a _ ha
      simp [conwayShortAxisRaw, Pi.single_eq_of_ne ha]
    · simp
  rw [conwayRawForm, hm, hs]
  have ht : conwayTensorForm (conwayShortAxisRaw r c).2.2 U.2.2 = 0 := by
    simp [conwayShortAxisRaw, conwayTensorForm]
  rw [ht]
  ring

/-- Actual double axial multiplication recovers the actual signed spin action
on every tensor coordinate. The axis rank-one term has zero tensor component. -/
theorem conwayShortAxisRaw_tensor_transposition_polynomial
    (r : GriessShortIndex) (c : ZMod 2) (U : ConwayRawSpace) (t : SpinIndex) (i : Fin 24) :
    14 * U.2.2 t i - 16 * (conwayRawProduct (conwayShortAxisRaw r c) U).2.2 t i +
      (conwayRawProduct (conwayShortAxisRaw r c)
        (conwayRawProduct (conwayShortAxisRaw r c) U)).2.2 t i =
      14 * conwayShortAxisSignedSpin r c U.2.2 t i := by
  rw [conwayShortAxisRaw_product_tensor, conwayShortAxisRaw_product_tensor,
    conwayShortAxisRaw_product_tensor]
  have h := congrArg (fun F : Module.End ℝ ConwayTensorSpace => F U.2.2 t i)
    (conwayShortAxisTensorOperator_transposition_polynomial r c)
  simp only [Module.End.mul_apply, Module.End.ofNat_apply, LinearMap.add_apply,
    LinearMap.sub_apply, pow_two, Pi.add_apply, Pi.sub_apply, nsmul_eq_mul,
    Nat.cast_ofNat] at h
  exact h.symm

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
