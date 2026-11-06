/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Fixed points of the actual Norton lattice action on the actual binary quotient. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderLeech
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonUOrderIntegralData

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

private theorem quarter_real : monsterNortonUMatrixQ.map (Rat.castHom ℝ) =
    (1/4 : ℝ) • monsterNortonUNumerator1.map (Int.castRingHom ℝ) := by
  ext i j
  change (((1/4 : ℚ) * (monsterNortonUNumerator1 i j : ℚ) : ℚ) : ℝ) =
    (1/4 : ℝ) * (monsterNortonUNumerator1 i j : ℝ)
  push_cast
  rfl

private theorem basis_real :
    monsterNortonUMatrixQ.map (Rat.castHom ℝ) * leechBasisMatrix.map (Int.castRingHom ℝ) =
      leechBasisMatrix.map (Int.castRingHom ℝ) *
        monsterNortonUIntegral.map (Int.castRingHom ℝ) := by
  rw [quarter_real, smul_mul_assoc, ← Matrix.map_mul, monsterNortonU_integral_certificate]
  ext i j
  change (1/4 : ℝ) * (((4 : ℤ) * (leechBasisMatrix * monsterNortonUIntegral) i j : ℤ) : ℝ) =
    (leechBasisMatrix.map (Int.castRingHom ℝ) *
      monsterNortonUIntegral.map (Int.castRingHom ℝ)) i j
  rw [← Matrix.map_mul]
  change (1/4 : ℝ) * (((4 : ℤ) * (leechBasisMatrix * monsterNortonUIntegral) i j : ℤ) : ℝ) =
    ((leechBasisMatrix * monsterNortonUIntegral) i j : ℝ)
  push_cast
  ring

/-- The checked integer matrix acts on the actual integral lattice basis. -/
theorem monsterNortonUFiber_leech_basis (z : Fin 24 → ℤ) :
    monsterNortonUFiber.val.2.val (leechCoordinateEmbedding (leechBasisMatrix *ᵥ z)) =
      leechCoordinateEmbedding (leechBasisMatrix *ᵥ (monsterNortonUIntegral *ᵥ z)) := by
  rw [monsterNortonUFiber_leech_matrix, leechCoordinateEmbedding_mulVec,
    Matrix.mulVec_mulVec, basis_real, ← Matrix.mulVec_mulVec,
    ← leechCoordinateEmbedding_mulVec, ← leechCoordinateEmbedding_mulVec]

/-- Its binary action is induced from that proved integral action. -/
theorem monsterNortonUFiber_leech_binary (v : Fin 24 → ZMod 2) :
    leechBinaryAction monsterNortonUFiber.val.2 v =
      (leechHyperbolicInverse * monsterNortonUIntegral.map (Int.castRingHom (ZMod 2)) *
        leechHyperbolicMatrix) *ᵥ v :=
  leechBinaryAction_of_basis_certificate _ _ monsterNortonUFiber_leech_basis v

private theorem fixed_zero (C J P PInv : Matrix (Fin 24) (Fin 24) (ZMod 2))
    (hP : P * PInv = 1) (hPInv : PInv * P = 1) (hJ : J * (C - 1) = 1)
    (v : Fin 24 → ZMod 2) (hv : (PInv * C * P) *ᵥ v = v) : v = 0 := by
  have hm : C *ᵥ (P *ᵥ v) = P *ᵥ v := by
    have hprod : P * (PInv * C * P) = C * P := by
      calc
        _ = P * (PInv * (C * P)) := congrArg (fun A => P * A) (mul_assoc PInv C P)
        _ = (P * PInv) * (C * P) := (mul_assoc P PInv (C * P)).symm
        _ = _ := by rw [hP, one_mul]
    have h := congrArg P.mulVec hv
    rw [Matrix.mulVec_mulVec, hprod, ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : (C - 1) *ᵥ (P *ᵥ v) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hm, sub_self]
  have hc := congrArg J.mulVec hz
  rw [Matrix.mulVec_mulVec, hJ, Matrix.one_mulVec, Matrix.mulVec_zero] at hc
  have h := congrArg PInv.mulVec hc
  rw [Matrix.mulVec_mulVec, hPInv, Matrix.one_mulVec, Matrix.mulVec_zero] at h
  exact h

/-- No nonzero vector of the actual quotient is fixed by the actual Norton action. -/
theorem monsterNortonUFiber_leech_binary_fixed (v : Fin 24 → ZMod 2)
    (hv : leechBinaryAction monsterNortonUFiber.val.2 v = v) : v = 0 := by
  rw [monsterNortonUFiber_leech_binary] at hv
  exact fixed_zero _ _ _ _ leechHyperbolicMatrix_inverse.1
    leechHyperbolicMatrix_inverse.2 monsterNortonU_fixed_point_certificate v hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
