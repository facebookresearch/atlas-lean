/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Orthogonality of the signed-short and spin-tensor local action blocks. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LocalExactness

@[expose] public section

namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped TensorProduct

/-- The signed short-vector action preserves its Euclidean pairing. -/
theorem localShortRepresentation_pairing (f : localFiberSubgroup)
    (x y : GriessShortIndex → ℝ) :
    (∑ r, localShortRepresentation f x r * localShortRepresentation f y r) =
      ∑ r, x r * y r := by
  change (∑ r, localShortOperator f x r * localShortOperator f y r) = _
  rw [← Equiv.sum_comp (griessShortPermutation f.val.2)
    (fun r => localShortOperator f x r * localShortOperator f y r)]
  simp_rw [localShortOperator_image]
  apply Finset.sum_congr rfl
  intro r _
  rw [show qSign (localShortPhase f r) * x r *
      (qSign (localShortPhase f r) * y r) =
      (qSign (localShortPhase f r) * qSign (localShortPhase f r)) * (x r * y r) by ring,
    qSign_sq, one_mul]

/-- The Euclidean form in the unit spin-tensor coordinates. -/
noncomputable def conwayTensorForm :
    (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] (SpinIndex → Fin 24 → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ t, ∑ i, x t i * y t i)
    (by intros; simp [add_mul, Finset.sum_add_distrib])
    (by intros; simp [mul_assoc, Finset.mul_sum])
    (by intros; simp [mul_add, Finset.sum_add_distrib])
    (by intros; simp [mul_left_comm, Finset.mul_sum])

/-- Pairings of pure tensors factor into pairings in the two factors. -/
theorem conwayTensorForm_tmul (a a' : SpinSpace) (b b' : Fin 24 → ℝ) :
    conwayTensorForm (conwayTensorCoordinates (a ⊗ₜ[ℝ] b))
      (conwayTensorCoordinates (a' ⊗ₜ[ℝ] b')) = spinPairing a a' * stdPairingFun b b' := by
  simp only [conwayTensorForm, LinearMap.mk₂_apply, conwayTensorCoordinates_tmul]
  simp_rw [show ∀ t i, a t * b i * (a' t * b' i) = (a t * a' t) * (b i * b' i) by
    intros; ring]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, spinPairing, stdPairingFun]

/-- Pure-tensor pairings are preserved by the local tensor action. -/
theorem localTensorAction_tmul_pairing (f : localFiberSubgroup)
    (a a' : SpinSpace) (b b' : Fin 24 → ℝ) :
    conwayTensorForm (conwayTensorCoordinates (localTensorAction f (a ⊗ₜ[ℝ] b)))
      (conwayTensorCoordinates (localTensorAction f (a' ⊗ₜ[ℝ] b'))) =
      conwayTensorForm (conwayTensorCoordinates (a ⊗ₜ[ℝ] b))
        (conwayTensorCoordinates (a' ⊗ₜ[ℝ] b')) := by
  change conwayTensorForm
    (conwayTensorCoordinates (TensorProduct.congr f.val.1.val f.val.2.val (a ⊗ₜ[ℝ] b)))
    (conwayTensorCoordinates (TensorProduct.congr f.val.1.val f.val.2.val (a' ⊗ₜ[ℝ] b'))) = _
  rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul, conwayTensorForm_tmul,
    conwayTensorForm_tmul]
  rw [f.val.1.property.2 a a', f.val.2.property.1 b b']

/-- Bilinearity extends pure-tensor orthogonality to the entire tensor product. -/
theorem localTensorAction_pairing (f : localFiberSubgroup)
    (x y : SpinSpace ⊗[ℝ] (Fin 24 → ℝ)) :
    conwayTensorForm (conwayTensorCoordinates (localTensorAction f x))
      (conwayTensorCoordinates (localTensorAction f y)) =
      conwayTensorForm (conwayTensorCoordinates x) (conwayTensorCoordinates y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | tmul a' b' => exact localTensorAction_tmul_pairing f a a' b b'
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

theorem coordinateGLTransport_apply {U V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module ℝ U] [Module ℝ V]
    (e : U ≃ₗ[ℝ] V) (a : U ≃ₗ[ℝ] U) (x : V) :
    coordinateGLTransport e a x = e (a (e.symm x)) := rfl

/-- The transported local tensor representation is orthogonal in unit coordinates. -/
theorem localTensorRepresentation_pairing (f : localFiberSubgroup)
    (x y : SpinIndex → Fin 24 → ℝ) :
    conwayTensorForm (localTensorRepresentation f x) (localTensorRepresentation f y) =
      conwayTensorForm x y := by
  simp only [localTensorRepresentation, MonoidHom.comp_apply, coordinateGLTransport_apply]
  rw [localTensorAction_pairing, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
