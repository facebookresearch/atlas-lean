/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.BinaryAutomorphism

/-! The canonical extraspecial lift has no cocode phase on a preserved cocode subspace. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private theorem beta_zero_left (x y : Fin 24 → ZMod 2)
    (hx : ∀ k : Fin 12, x (Fin.castAdd 12 k) = 0) : qBeta x y = 0 := by
  simp only [qBeta, hx, zero_mul, Finset.sum_const_zero]

/-- A binary map preserving pure cocodes gives zero correction on every pure cocode. -/
theorem generatedSeventh_cocode_correction_zero
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2))
    (hR : ∀ x : Fin 24 → ZMod 2, (∀ k : Fin 12, x (Fin.castAdd 12 k) = 0) →
      ∀ k : Fin 12, R x (Fin.castAdd 12 k) = 0)
    (x : Fin 24 → ZMod 2) (hx : ∀ k : Fin 12, x (Fin.castAdd 12 k) = 0) :
    qCentralCorrection R x = 0 := by
  have hsingle (i : Fin 12) :
      ∀ k : Fin 12, (Pi.single (Fin.natAdd 12 i) 1 : Fin 24 → ZMod 2)
        (Fin.castAdd 12 k) = 0 := by
    intro k
    have hne : Fin.castAdd 12 k ≠ Fin.natAdd 12 i := by
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
      omega
    simp only [Pi.single_apply, ite_eq_right hne]
  have hm (i j : Fin 12) :
      qCorrectionMatrix R (Fin.natAdd 12 i) (Fin.natAdd 12 j) = 0 := by
    unfold qCorrectionMatrix
    rw [qCocycleDifference_apply, beta_zero_left _ _ (hR _ (hsingle i)),
      beta_zero_left _ _ (hsingle i), add_zero]
    simp only [ite_self]
  rw [qCentralCorrection, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  refine Fin.addCases (m := 12) (n := 12) ?_ ?_ i
  · intro a
    simp only [hx, zero_mul]
  · intro a
    refine Fin.addCases (m := 12) (n := 12) ?_ ?_ j
    · intro b
      simp only [hx, mul_zero]
    · intro b
      simp only [hm, mul_zero, zero_mul]

/-- Strict triangularity makes the canonical central correction zero on each basis vector. -/
theorem generatedSeventh_correction_single_zero
    (R : (Fin 24 → ZMod 2) ≃ₗ[ZMod 2] (Fin 24 → ZMod 2)) (i : Fin 24) :
    qCentralCorrection R (Pi.single i 1) = 0 := by
  rw [qCentralCorrection, LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toBilin'_single]
  simp only [qCorrectionMatrix, lt_irrefl, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
