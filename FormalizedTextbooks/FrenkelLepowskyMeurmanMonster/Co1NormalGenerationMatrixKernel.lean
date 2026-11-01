/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual Conway matrix action is faithful modulo the two scalar signs. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechBinaryFaithfulness

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Rank-one symmetric matrices recover products of coordinate pairings. -/
theorem conway_rank_one_pairing (x u v : Fin 24 → ℝ) :
    Matrix.toBilin' (fun i j => x i * x j : Matrix (Fin 24) (Fin 24) ℝ) u v =
      stdPairingFun x u * stdPairingFun x v := by
  rw [Matrix.toBilin'_apply]
  simp only [stdPairingFun, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Orthogonality identifies inverse covectors with forward vectors. -/
theorem stdPairing_isometry_inverse_right (e : leechIsomSubgroup) (x y : Fin 24 → ℝ) :
    stdPairingFun x (e.val.symm y) = stdPairingFun (e.val x) y := by
  have h := e.property.1 x (e.val.symm y)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Triviality on all symmetric matrices preserves each rank-one coordinate product. -/
theorem conwayMatrix_symmetric_trivial_rank_one (e : leechIsomSubgroup)
    (he : ∀ a : Matrix (Fin 24) (Fin 24) ℝ,
      (∀ i j, a i j = a j i) → conwayMatrixAction e a = a)
    (x : Fin 24 → ℝ) (i j : Fin 24) :
    (e.val x) i * (e.val x) j = x i * x j := by
  have hm := he (fun k l => x k * x l) (fun k l => mul_comm _ _)
  have hb := congrArg (fun a : Matrix (Fin 24) (Fin 24) ℝ =>
    Matrix.toBilin' a (leechUnit i) (leechUnit j)) hm
  rw [conwayMatrixAction_pairing e (fun k l => x k * x l) (leechUnit i) (leechUnit j),
    conway_rank_one_pairing, conway_rank_one_pairing,
    stdPairing_isometry_inverse_right, stdPairing_isometry_inverse_right] at hb
  have hu (z : Fin 24 → ℝ) (k : Fin 24) : stdPairingFun z (leechUnit k) = z k := by
    simp [stdPairingFun, leechUnit, Pi.single_apply, mul_ite]
  simpa only [hu] using hb

/-- An isometry acting trivially on symmetric matrices is one of the two actual signs. -/
theorem conwayMatrix_symmetric_trivial_mem_signs (e : leechIsomSubgroup)
    (he : ∀ a : Matrix (Fin 24) (Fin 24) ℝ,
      (∀ i j, a i j = a j i) → conwayMatrixAction e a = a) : e ∈ signsSubgroup := by
  have hpair : ∀ i j : Fin 24, i ≠ j → ∃ a : ℝ, (a = 1 ∨ a = -1) ∧
      e.val (leechUnit i + leechUnit j) = a • (leechUnit i + leechUnit j) := by
    intro i j hij
    let x := leechUnit i + leechUnit j
    have hx : x i = 1 := by simp [x, leechUnit, hij.symm]
    have hi := conwayMatrix_symmetric_trivial_rank_one e he x i i
    rw [hx] at hi
    have ha : (e.val x) i = 1 ∨ (e.val x) i = -1 := by
      exact mul_self_eq_one_iff.mp (by simpa only [one_mul] using hi)
    refine ⟨(e.val x) i, ha, ?_⟩
    ext k
    have hk := conwayMatrix_symmetric_trivial_rank_one e he x i k
    rw [hx, one_mul] at hk
    change (e.val x) k = (e.val x) i * x k
    rcases ha with ha | ha <;> rw [ha] at hk ⊢ <;> linarith
  obtain ⟨a, ha, hx⟩ := linear_isometry_pair_eigenvectors_scalar e hpair
  rcases ha with rfl | rfl
  · left
    apply LinearEquiv.ext
    intro x
    simpa only [one_smul, LinearEquiv.coe_one, id_eq] using hx x
  · right
    intro x
    simpa only [neg_one_smul] using hx x

/-- Equal actions on the symmetric matrix constituent give equal actual Conway classes. -/
theorem conwayMatrix_symmetric_eq_quotient (e f : leechIsomSubgroup)
    (hef : ∀ a : Matrix (Fin 24) (Fin 24) ℝ,
      (∀ i j, a i j = a j i) → conwayMatrixAction e a = conwayMatrixAction f a) :
    (QuotientGroup.mk e : Co1) = QuotientGroup.mk f := by
  apply QuotientGroup.eq_iff_div_mem.mpr
  apply conwayMatrix_symmetric_trivial_mem_signs
  intro a ha
  change conwayMatrixAction (e * f⁻¹) a = a
  rw [map_mul, LinearEquiv.mul_apply]
  rw [hef _ (conwayMatrixAction_symmetric f⁻¹ a ha)]
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

/-- The matrix constituent determines the actual Conway projection of a local element. -/
theorem projH_eq_of_matrix_action (h : H) (e : leechIsomSubgroup)
    (he : ∀ x : GriessSpace, (griessConwayEncode (rhoLocal h x)).1 =
      conwayMatrixAction e (griessConwayEncode x).1) :
    projH h = (QuotientGroup.mk e : Co1) := by
  revert he
  refine Quotient.inductionOn h ?_
  intro f hf
  change (QuotientGroup.mk f.val.2 : Co1) = QuotientGroup.mk e
  apply conwayMatrix_symmetric_eq_quotient
  intro a ha
  let raw : ConwayRawSpace := (a, (0,0))
  have hx := griessConwayEncode_decode raw ha
  have hh := hf (griessConwayDecode raw)
  have hl := localGriessRepresentation_encode f (griessConwayDecode raw)
  have hm := congrArg (fun b : ConwayRawSpace => b.1) hl
  change (griessConwayEncode (rhoLocal (QuotientGroup.mk f) (griessConwayDecode raw))).1 =
      conwayMatrixAction f.val.2 (griessConwayEncode (griessConwayDecode raw)).1 at hm
  rw [hm, hx] at hh
  exact hh

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
