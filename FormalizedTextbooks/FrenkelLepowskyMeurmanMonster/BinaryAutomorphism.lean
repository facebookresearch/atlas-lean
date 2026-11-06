/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Lifting a binary isometry of the extraspecial quadratic form to an automorphism of Q.
-/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Definitions

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative NormalizedCocycleExtension
set_option backward.isDefEq.respectTransparency false

/-- Difference between the transported coordinate cocycle and the original cocycle. -/
noncomputable def qCocycleDifference
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :
    LinearMap.BilinForm (ZMod 2) (Fin 24 → ZMod 2) :=
  qBilin.compl₁₂ R.toLinearMap R.toLinearMap + qBilin

@[simp] theorem qCocycleDifference_apply
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) (x y : Fin 24 → ZMod 2) :
    qCocycleDifference R x y = qBeta (R x) (R y) + qBeta x y := rfl

/-- Preservation of squares makes the cocycle difference alternating. -/
theorem qCocycleDifference_diagonal
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) (x : Fin 24 → ZMod 2) :
    qCocycleDifference R x x = 0 := by
  change qBeta (R x) (R x) + qBeta x x = 0
  have hx := hR x
  change qBeta (R x) (R x) = qBeta x x at hx
  rw [hx, ZModModule.add_self]

/-- An alternating bilinear form in characteristic two is symmetric. -/
theorem qCocycleDifference_symmetric
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) (x y : Fin 24 → ZMod 2) :
    qCocycleDifference R x y = qCocycleDifference R y x := by
  have h := qCocycleDifference_diagonal R hR (x + y)
  simp only [map_add, LinearMap.add_apply,
    qCocycleDifference_diagonal R hR x, qCocycleDifference_diagonal R hR y,
    zero_add, add_zero] at h
  rw [add_comm] at h
  calc
    qCocycleDifference R x y =
        (qCocycleDifference R x y + qCocycleDifference R y x) + qCocycleDifference R y x := by
      rw [add_assoc, ZModModule.add_self, add_zero]
    _ = qCocycleDifference R y x := by rw [h, zero_add]

/-- Strictly upper triangular coefficient matrix whose polarization is the cocycle difference. -/
noncomputable def qCorrectionMatrix
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :
    Matrix (Fin 24) (Fin 24) (ZMod 2) := fun i j =>
  if i < j then qCocycleDifference R (Pi.single i 1) (Pi.single j 1) else 0

/-- The quadratic cochain used to correct the central bit. -/
noncomputable def qCentralCorrection
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) :
    QuadraticMap (ZMod 2) (Fin 24 → ZMod 2) (ZMod 2) :=
  (qCorrectionMatrix R).toBilin'.toQuadraticMap

/-- The correction's polarization is exactly the alternating cocycle difference. -/
theorem qCentralCorrection_polar
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) :
    (qCentralCorrection R).polarBilin = qCocycleDifference R := by
  apply LinearMap.ext_basis (Pi.basisFun (ZMod 2) (Fin 24))
    (Pi.basisFun (ZMod 2) (Fin 24))
  intro i j
  simp only [Pi.basisFun_apply, qCentralCorrection, QuadraticMap.polarBilin_apply_apply,
    LinearMap.BilinMap.polar_toQuadraticMap, Matrix.toBilin'_single, qCorrectionMatrix]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [ite_eq_left h, ite_eq_right (not_lt_of_ge h.le), add_zero]
  · rw [ite_eq_right (lt_irrefl _), zero_add]
    exact (qCocycleDifference_diagonal R hR _).symm
  · rw [ite_eq_right (not_lt_of_ge h.le), ite_eq_left h, zero_add]
    exact qCocycleDifference_symmetric R hR _ _

/-- The cochain identity that turns the linear isometry into a group homomorphism. -/
theorem qCentralCorrection_add
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) (x y : Fin 24 → ZMod 2) :
    qCentralCorrection R (x + y) =
      qCentralCorrection R x + qCentralCorrection R y + qBeta (R x) (R y) + qBeta x y := by
  rw [QuadraticMap.map_add (qCentralCorrection R),
    ← QuadraticMap.polarBilin_apply_apply, qCentralCorrection_polar R hR,
    qCocycleDifference_apply]
  abel

/-- Correcting the central coefficient produces a homomorphism of the actual extension. -/
noncomputable def qCorrectedLinearHom
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (θ : (Fin 24 → ZMod 2) → ZMod 2) (hzero : θ 0 = 0)
    (hadd : ∀ x y, θ (x + y) = θ x + θ y + qBeta (R x) (R y) + qBeta x y) : Q →* Q where
  toFun g := ⟨ofAdd (R (toAdd g.base)),
    ofAdd (toAdd g.coeff + θ (toAdd g.base))⟩
  map_one' := by
    apply Extension.ext
    · apply toAdd.injective
      exact R.map_zero
    · apply toAdd.injective
      change 0 + θ 0 = 0
      simp [hzero]
  map_mul' g h := by
    apply Extension.ext
    · apply toAdd.injective
      exact R.map_add (toAdd g.base) (toAdd h.base)
    · apply toAdd.injective
      change (toAdd g.coeff + toAdd h.coeff + qBeta (toAdd g.base) (toAdd h.base)) +
          θ (toAdd g.base + toAdd h.base) =
        (toAdd g.coeff + θ (toAdd g.base)) +
          (toAdd h.coeff + θ (toAdd h.base)) +
          qBeta (R (toAdd g.base)) (R (toAdd h.base))
      rw [hadd]
      calc
        _ = (toAdd g.coeff + θ (toAdd g.base)) +
            (toAdd h.coeff + θ (toAdd h.base)) +
            qBeta (R (toAdd g.base)) (R (toAdd h.base)) +
            (qBeta (toAdd g.base) (toAdd h.base) + qBeta (toAdd g.base) (toAdd h.base)) := by abel
        _ = _ := by rw [ZModModule.add_self, add_zero]

/-- An explicit inverse subtracts the same correction after applying the inverse base map.
In characteristic two subtraction equals addition. -/
noncomputable def qCorrectedLinearEquiv
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (θ : (Fin 24 → ZMod 2) → ZMod 2) (hzero : θ 0 = 0)
    (hadd : ∀ x y, θ (x + y) = θ x + θ y + qBeta (R x) (R y) + qBeta x y) : MulAut Q where
  toFun := qCorrectedLinearHom R θ hzero hadd
  invFun g := ⟨ofAdd (R.symm (toAdd g.base)),
    ofAdd (toAdd g.coeff + θ (R.symm (toAdd g.base)))⟩
  left_inv g := by
    apply Extension.ext
    · apply toAdd.injective
      exact R.symm_apply_apply _
    · apply toAdd.injective
      change (toAdd g.coeff + θ (toAdd g.base)) +
        θ (R.symm (R (toAdd g.base))) = toAdd g.coeff
      rw [R.symm_apply_apply, add_assoc, ZModModule.add_self, add_zero]
  right_inv g := by
    apply Extension.ext
    · apply toAdd.injective
      exact R.apply_symm_apply _
    · apply toAdd.injective
      change (toAdd g.coeff + θ (R.symm (toAdd g.base))) +
        θ (R.symm (toAdd g.base)) = toAdd g.coeff
      rw [add_assoc, ZModModule.add_self, add_zero]
  map_mul' := (qCorrectedLinearHom R θ hzero hadd).map_mul

/-- The cocycle correction associated to a binary isometry, bundled as a group homomorphism. -/
noncomputable def qBinaryIsometryLiftHom
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) : Q →* Q :=
  qCorrectedLinearHom R (qCentralCorrection R) (QuadraticMap.map_zero _)
    (qCentralCorrection_add R hR)

/-- The binary isometry lifts to an automorphism with a corrected central coefficient. -/
noncomputable def qBinaryIsometryLift
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) : MulAut Q :=
  qCorrectedLinearEquiv R (qCentralCorrection R) (QuadraticMap.map_zero _)
    (qCentralCorrection_add R hR)

/-- The lifted automorphism induces precisely the requested binary isometry. -/
theorem qBinaryAction_isometryLift
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) :
    qBinaryAction (qBinaryIsometryLift R hR) = R := by
  apply LinearEquiv.ext
  intro v
  rw [← show toAdd (qQuotHom (⟨ofAdd v, 1⟩ : Q)) = v from rfl,
    qBinaryAction_apply]
  rfl

/-- Every binary isometry lifts to an automorphism of the extraspecial coordinate group. -/
theorem exists_qBinaryAction_lift
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) :
    ∃ a : MulAut Q, qBinaryAction a = R :=
  ⟨qBinaryIsometryLift R hR, qBinaryAction_isometryLift R hR⟩

/-- The lift fixes each central bit, as required for the spin representation. -/
theorem qBinaryIsometryLift_central
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x, squareQuad (R x) = squareQuad x) (c : ZMod 2) :
    qBinaryIsometryLift R hR (qCentral c) = qCentral c := by
  apply Extension.ext
  · apply toAdd.injective
    exact R.map_zero
  · apply toAdd.injective
    change c + qCentralCorrection R 0 = c
    rw [QuadraticMap.map_zero, add_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
